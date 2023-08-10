module Tests where

import Control.Monad
import Data.Foldable
import GHC.Conc
import GHC.TypeLits
import Runtime (evaluate)
import System.Random (randomIO)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Types

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
