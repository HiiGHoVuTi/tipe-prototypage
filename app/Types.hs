module Types where

import Control.DeepSeq
import Data.Data
import GHC.Conc
import GHC.Generics
import GHC.TypeLits
import System.Random (randomIO)

type Identifier = Int

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

-- TODO(Maxime): equality algorithm
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
