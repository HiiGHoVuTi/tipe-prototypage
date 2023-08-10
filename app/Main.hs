module Main where

import Control.DeepSeq
import Control.Monad
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
  | Variable (Maybe NodeRef)
  | Application NodeRef NodeRef
  | Constructor Identifier [NodeRef]
  | Operator Char NodeRef NodeRef
  deriving (Eq, Generic, Data, NFData)

showNode :: Node -> String
showNode = show . toConstr

createDup :: Identifier -> NodeRef -> STM (NodeRef, NodeRef, NodeRef)
createDup ι α = do
  δ₁ <- newNodeRef (Variable Nothing)
  δ₂ <- newNodeRef (Variable Nothing)
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
nDuplicates :: Nat -> NodeRef -> IO [NodeRef]
nDuplicates 0 ____ = pure []
nDuplicates 1 node = pure [node]
nDuplicates n node = do
  ι <- randomIO
  (latestClone : rest) <- nDuplicates (n - 1) node
  (_, δ₁, δ₂) <- atomically do createDup ι latestClone
  pure (δ₁ : δ₂ : rest)

lambdaHelper :: (NodeRef -> STM NodeRef) -> STM NodeRef
lambdaHelper body = do
  α <- newNodeRef (Variable Nothing)
  ν <- body α
  newNodeRef (Lambda α ν)

evaluate :: NodeRef -> IO Node
evaluate root =
  readNodeRefIO root >>= \case
    Variable (Just α) -> evaluate α
    Duplicated ρ -> do
      Duplication ι v (δ₁, δ₂) <- readNodeRefIO ρ
      -- NOTE(Maxime): avoid extra work, evaluate once
      β <- evaluate v
      atomically do writeNodeRef v β
      unless (root `elem` [δ₁, δ₂]) (error "INCOHERENT")
      case β of
        Constructor μ xs ->
          atomically do
            (_, δ₁s, δ₂s) <- unzip3 <$> traverse (createDup ι) xs
            writeNodeRef δ₁ (Constructor μ δ₁s)
            writeNodeRef δ₂ (Constructor μ δ₂s)
            *> evaluate root
        Lambda arg body ->
          atomically do
            arg'₁ <- newNodeRef (Variable Nothing)
            arg'₂ <- newNodeRef (Variable Nothing)
            (_, body'₁, body'₂) <- createDup ι body
            σ <- newNodeRef (Superposition ι (arg'₁, arg'₂))
            writeNodeRef arg (Variable (Just σ))
            writeNodeRef δ₁ (Lambda arg'₁ body'₁)
            writeNodeRef δ₂ (Lambda arg'₂ body'₂)
            *> evaluate root
        Superposition ι' (σ₁, σ₂)
          | ι == ι' -> do
              atomically do
                writeNodeRef δ₁ =<< readNodeRef σ₁
                writeNodeRef δ₂ =<< readNodeRef σ₂
                *> evaluate root
          | otherwise -> do
              putStrLn "ohno" :: IO ()
              (ι₁, ι₂) <- bisequence (randomIO, randomIO)
              atomically do
                (_, δ₁σ₁, δ₂σ₁) <- createDup ι₁ σ₁
                (_, δ₁σ₂, δ₂σ₂) <- createDup ι₂ σ₂
                writeNodeRef δ₁ (Superposition ι₁ (δ₁σ₁, δ₁σ₂))
                writeNodeRef δ₂ (Superposition ι₂ (δ₂σ₁, δ₂σ₂))
              evaluate root
        n@IntegerValue {} -> do
          atomically do
            writeNodeRef δ₁ n
            writeNodeRef δ₂ n
            *> evaluate root
        -- NOTE(Maxime): already in nf
        _ -> error "invariant broken"
    Application φ α ->
      readNodeRefIO φ >>= \case
        Lambda arg body ->
          atomically do
            writeNodeRef arg (Variable (Just α))
            *> evaluate body
        Superposition ι (σ₁, σ₂) ->
          atomically do
            (_, α₁, α₂) <- createDup ι α
            σ₁' <- newNodeRef (Application σ₁ α₁)
            σ₂' <- newNodeRef (Application σ₂ α₂)
            writeNodeRef root (Superposition ι (σ₁', σ₂'))
            *> evaluate root
        f -> do
          ψ <- evaluate φ
          atomically do writeNodeRef φ ψ
          -- TODO(Maxime): avoid this using a whnf detector
          when (f == ψ) (error ("impossible to evaluate " <> showNode f))
          evaluate root
    Operator c x y -> do
      Just op <- pure $ lookup c [('+', (+)), ('-', (-)), ('*', (*)), ('/', quot), ('%', rem)]
      (,) <$> evaluate x <*> evaluate y >>= \case
        (IntegerValue a, IntegerValue b) -> pure (IntegerValue (a `op` b))
        _ -> error "called operator on non-integers"
    node -> pure node

-- tests

prop_vie_est_belle :: Bool
prop_vie_est_belle = True

prop_id_on_int :: Int -> Property
prop_id_on_int i = monadicIO $ run do
  let expected = IntegerValue i
  value <- newNodeRefIO expected
  lambda <- atomically do lambdaHelper pure
  root <- newNodeRefIO (Application lambda value)
  result <- evaluate root
  pure (result == expected)

prop_dup_id :: Int -> Property
prop_dup_id i = monadicIO $ run do
  let expected = IntegerValue i
  input <- newNodeRefIO expected
  lambda <- atomically do lambdaHelper pure
  (_, clone1, _) <- atomically do createDup 0 lambda
  root <- newNodeRefIO (Application clone1 input)
  result <- evaluate root
  pure (result == expected)

prop_dup_cons :: Word -> Property
prop_dup_cons i = monadicIO $ run do
  lab <- randomIO
  let expected = Constructor i []
  input <- newNodeRefIO expected
  (_, out1, out2) <- atomically do createDup lab input
  res1 <- evaluate out1
  res2 <- evaluate out2
  pure (expected == res1 && expected == res2)

prop_not :: NodeRef -> Int -> IO Bool
prop_not f p = do
  dummie1 <- newNodeRefIO (IntegerValue 0)
  dummie2 <- newNodeRefIO (IntegerValue 1)
  partial <- newNodeRefIO (Application f dummie1)
  root <- newNodeRefIO (Application partial dummie2)
  result <- evaluate root
  pure (result == IntegerValue p)

prop_not_composition_naive :: Nat -> IO Node
prop_not_composition_naive n = do
  true <- atomically do lambdaHelper \t -> lambdaHelper \_ -> pure t
  notF <- atomically do
    lambdaHelper \p -> lambdaHelper \t -> lambdaHelper \f -> do
      partial <- newNodeRef (Application p f)
      newNodeRef (Application partial t)
  nots <- nDuplicates n notF
  result <- atomically do foldlM ((newNodeRef .) . flip Application) true nots
  evaluate result

prop_not_composition :: Nat -> IO Node
prop_not_composition n = do
  true <- atomically do lambdaHelper \t -> lambdaHelper \_ -> pure t
  notF <- atomically do
    lambdaHelper \p -> lambdaHelper \t -> lambdaHelper \f -> do
      partial <- newNodeRef (Application p f)
      newNodeRef (Application partial t)
  let mkff = do
        i <- randomIO
        atomically do
          lambdaHelper \f -> lambdaHelper \x -> do
            (_, f1, f2) <- createDup i f
            partial <- newNodeRef (Application f1 x)
            newNodeRef (Application f2 partial)
  -- forced to cheat here, TODO(Maxime): use constructors to solve this
  ffs <- replicateM (fromEnum n) mkff
  finalF <- atomically do foldlM ((newNodeRef .) . flip Application) notF ffs
  result <- newNodeRefIO (Application finalF true)
  evaluate result

prop_op :: Int -> Int -> Property
prop_op a' b' = monadicIO $ run do
  a <- newNodeRefIO (IntegerValue a')
  b <- newNodeRefIO (IntegerValue b')
  (_, a1, a2) <- atomically do createDup 0 a
  partial <- newNodeRefIO (Operator '+' a1 b)
  root' <- newNodeRefIO (Operator '*' partial a2)
  (_, root, _) <- atomically do createDup 1 root'
  result <- evaluate root
  pure (result == IntegerValue ((a' + b') * a'))

main :: IO ()
main =
  defaultMain
    [ testProperty "tautology" prop_vie_est_belle,
      bgroup
        "interpreter correctness"
        [ testProperty "identity" prop_id_on_int,
          bgroup
            "duplication"
            [ testProperty "duplication of the identity" prop_dup_id,
              testProperty "duplication of a constructor" prop_dup_cons
            ],
          bgroup
            "operations"
            [ testProperty "basic operators" prop_op
            ]
        ],
      bgroup
        "boolean not (Church)"
        [ testProperty
            "not composition correctness"
            $ property \n -> n >= 0 ==> monadicIO $ run do
              newF <- newNodeRefIO =<< prop_not_composition_naive (toEnum n)
              prop_not newF (n `mod` 2),
          testProperty
            "not 2^n composition correctness"
            $ property \n -> n >= 0 ==> monadicIO $ run do
              newF <- newNodeRefIO =<< prop_not_composition (toEnum n)
              prop_not newF (fromEnum (n == 0)),
          bgroup
            "no fusion"
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
              pure $ bench (show @Nat (2 ^ i)) $ nfAppIO prop_not_composition i
        ]
    ]
