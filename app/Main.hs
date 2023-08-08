module Main where

import Control.DeepSeq
import Data.Bitraversable
import Data.Data
import Data.Foldable
import GHC.Conc
import GHC.Generics
import GHC.TypeLits
import System.Random (randomIO)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.Tasty.Bench
import Test.Tasty.QuickCheck

-- types

type Identifier = Word

newtype NodeRef = MkRef {getRef :: TVar Node}
  deriving (Eq, Typeable)

instance NFData NodeRef where rnf x = seq x ()

-- FIXME(Maxime): unlawful
instance Data NodeRef where
  dataTypeOf _ = mkIntType "NodeRef"
  toConstr a = mkConstr (dataTypeOf a) "NodeRef" [] Data.Data.Prefix
  gunfold _ _ _ = undefined

newNodeRef :: Node -> STM NodeRef
newNodeRef = fmap MkRef . newTVar

newNodeRefIO :: Node -> IO NodeRef
newNodeRefIO = fmap MkRef . newTVarIO

readNodeRef :: NodeRef -> STM Node
readNodeRef = readTVar . getRef

readNodeRefIO :: NodeRef -> IO Node
readNodeRefIO = readTVarIO . getRef

writeNodeRef :: NodeRef -> Node -> STM ()
writeNodeRef = writeTVar . getRef

data Node
  = Superposition Identifier (NodeRef, NodeRef)
  | Duplication Identifier NodeRef (NodeRef, NodeRef)
  | Duplicated NodeRef
  | IntegerValue Int
  | Lambda NodeRef NodeRef
  | Variable
  | Application NodeRef NodeRef
  | Constructor Identifier [NodeRef]
  deriving (Eq, Generic, Data, NFData)

showNode :: Node -> String
showNode = show . toConstr

createDup :: Identifier -> NodeRef -> STM (NodeRef, NodeRef, NodeRef)
createDup ι α = do
  δ₁ <- newNodeRef Variable
  δ₂ <- newNodeRef Variable
  ρ <- newNodeRef (Duplication ι α (δ₁, δ₂))
  writeNodeRef δ₁ (Duplicated ρ)
  writeNodeRef δ₂ (Duplicated ρ)
  pure (ρ, δ₁, δ₂)

duplicationOf :: Node -> IO (NodeRef, NodeRef, NodeRef)
duplicationOf ν = do
  α <- newNodeRefIO ν
  ι <- randomIO
  atomically do createDup ι α

-- TODO(Maxime): verify whether you need different identifiers
nDuplicates :: Identifier -> Nat -> NodeRef -> STM [NodeRef]
nDuplicates _ 0 ____ = pure []
nDuplicates _ 1 node = pure [node]
nDuplicates ι n node = do
  nDuplicates ι (n - 1) node >>= \case
    [] -> error "impossible"
    (latestClone : rest) -> do
      (_, δ₁, δ₂) <- createDup ι latestClone
      pure (δ₁ : δ₂ : rest)

lambdaHelper :: (NodeRef -> STM NodeRef) -> STM NodeRef
lambdaHelper body = do
  α <- newNodeRef Variable
  ν <- body α
  newNodeRef (Lambda α ν)

evaluate :: NodeRef -> IO Node
evaluate root =
  readNodeRefIO root >>= \case
    Duplicated ρ -> do
      Duplication ι v (δ₁, δ₂) <- readNodeRefIO ρ
      readNodeRefIO v >>= \case
        Constructor μ xs ->
          atomically do
            (_, δ₁s, δ₂s) <- unzip3 <$> traverse (createDup ι) xs
            writeNodeRef δ₁ (Constructor μ δ₁s)
            writeNodeRef δ₂ (Constructor μ δ₂s)
            *> evaluate δ₁
        Lambda arg body ->
          atomically do
            arg'₁ <- newNodeRef Variable
            arg'₂ <- newNodeRef Variable
            (_, body'₁, body'₂) <- createDup ι body
            writeNodeRef arg (Superposition ι (arg'₁, arg'₂))
            writeNodeRef δ₁ (Lambda arg'₁ body'₁)
            writeNodeRef δ₂ (Lambda arg'₂ body'₂)
            *> evaluate δ₁
        Superposition ι' (σ₁, σ₂)
          | ι == ι' ->
              atomically do
                writeNodeRef δ₁ =<< readNodeRef σ₁
                writeNodeRef δ₂ =<< readNodeRef σ₂
                *> evaluate δ₁
          | otherwise -> do
              (ι₁, ι₂) <- bisequence (randomIO, randomIO)
              atomically do
                (_, δ₁σ₁, δ₂σ₁) <- createDup ι₁ σ₁
                (_, δ₁σ₂, δ₂σ₂) <- createDup ι₂ σ₂
                writeNodeRef δ₁ (Superposition ι₁ (δ₁σ₁, δ₁σ₂))
                writeNodeRef δ₂ (Superposition ι₂ (δ₂σ₁, δ₂σ₂))
              evaluate δ₁
        n ->
          atomically do
            writeNodeRef δ₁ n
            writeNodeRef δ₂ n
            *> evaluate δ₁
    -- _n -> error "invariant broken"
    Application φ α ->
      readNodeRefIO φ >>= \case
        Lambda arg body ->
          atomically do
            writeNodeRef arg =<< readNodeRef α
            *> evaluate body
        Superposition ι (σ₁, σ₂) ->
          atomically do
            writeNodeRef σ₁ (Application φ σ₁)
            writeNodeRef σ₂ (Application φ σ₂)
            writeNodeRef root (Superposition ι (σ₁, σ₂))
            *> evaluate root
        _ -> do
          ψ <- evaluate φ
          atomically do writeNodeRef φ ψ
          evaluate root
    node -> pure node

-- tests

prop_vie_est_belle :: Bool
prop_vie_est_belle = True

prop_id_on_int :: Int -> Property
prop_id_on_int i = monadicIO $ run do
  let expected = IntegerValue i
  valu <- newNodeRefIO expected
  ldva <- newNodeRefIO Variable
  lmbd <- newNodeRefIO (Lambda ldva ldva)
  root <- newNodeRefIO (Application lmbd valu)
  result <- evaluate root
  pure (result == expected)

prop_dup_id :: Int -> Property
prop_dup_id i = monadicIO $ run do
  let expected = IntegerValue i
  inpu <- newNodeRefIO expected
  ldva <- newNodeRefIO Variable
  lmid <- newNodeRefIO (Lambda ldva ldva)
  (_, clo1, _) <- atomically do createDup 0 lmid
  root <- newNodeRefIO (Application clo1 inpu)
  result <- evaluate root
  pure (result == expected)

prop_not_composition_naive :: Nat -> IO Node
prop_not_composition_naive n = do
  i <- randomIO
  true <- atomically do lambdaHelper \t -> lambdaHelper \_ -> pure t
  notF <- atomically do
    lambdaHelper \t -> lambdaHelper \f -> lambdaHelper \p -> do
      partial <- newNodeRef (Application p f)
      newNodeRef (Application partial t)
  nots <- atomically do nDuplicates i n notF
  result <- atomically do foldlM ((newNodeRef .) . Application) true nots
  evaluate result

prop_not_composition :: Nat -> IO Node
prop_not_composition n = do
  i <- randomIO
  true <- atomically do lambdaHelper \t -> lambdaHelper \_ -> pure t
  notF <- atomically do
    lambdaHelper \t -> lambdaHelper \f -> lambdaHelper \p -> do
      partial <- newNodeRef (Application p f)
      newNodeRef (Application partial t)
  ff <- atomically do
    lambdaHelper \f -> lambdaHelper \x -> do
      partial <- newNodeRef (Application f x)
      newNodeRef (Application f partial)
  ffs <- atomically do nDuplicates i n ff
  finalF <- atomically do foldlM ((newNodeRef .) . Application) notF ffs
  result <- newNodeRefIO (Application finalF true)
  evaluate result

main :: IO ()
main =
  defaultMain
    [ testProperty "tautology" prop_vie_est_belle,
      bgroup
        "correctness"
        [ testProperty "identity" prop_id_on_int,
          bgroup
            "duplication"
            [ testProperty "duplication of the identity" prop_dup_id
            ]
        ],
      bgroup
        "boolean not (Church)"
        [ testProperties
            "not composition correctness"
            [],
          bgroup
            "no fusion"
            -- TODO
            do
              i <- [0, 2 :: Int .. 9]
              let n = 2 ^ i
              pure $
                bench (show n) $
                  nfAppIO prop_not_composition_naive n,
          bgroup
            "fusion"
            do
              i <- [0, 2 .. 64]
              pure $ bench (show @Nat (2^i)) $ nfAppIO prop_not_composition i
        ]
    ]
