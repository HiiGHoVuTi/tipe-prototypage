module Tests where

import Control.Monad
import Data.Foldable
import Data.IntMap.Strict
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
  result <- evaluate mempty root
  pure (result == expected)

prop_dup_id :: Int -> Property
prop_dup_id i = monadicIO $ run do
  let expected = IntegerValue i
  input <- newNodeRefIO expected
  lambda <- atomically do lambdaHelper pure
  (_, clone1, _) <- atomically do createDup 0 lambda
  root <- newNodeRefIO (Application clone1 input)
  result <- evaluate mempty root
  pure (result == expected)

prop_dup_cons :: Identifier -> Property
prop_dup_cons i = monadicIO $ run do
  lab <- randomIO
  let expected = Constructor i []
  input <- newNodeRefIO expected
  (_, out1, out2) <- atomically do createDup lab input
  res1 <- evaluate mempty out1
  res2 <- evaluate mempty out2
  pure (expected == res1 && expected == res2)

prop_not :: NodeRef -> Int -> IO Bool
prop_not f p = do
  dummie1 <- newNodeRefIO (IntegerValue 0)
  dummie2 <- newNodeRefIO (IntegerValue 1)
  partial <- newNodeRefIO (Application f dummie1)
  root <- newNodeRefIO (Application partial dummie2)
  result <- evaluate mempty root
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
  evaluate mempty result

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
  evaluate mempty result

prop_op :: Int -> Int -> Property
prop_op a' b' = monadicIO $ run do
  a <- newNodeRefIO (IntegerValue a')
  b <- newNodeRefIO (IntegerValue b')
  (_, a1, a2) <- atomically do createDup 0 a
  partial <- newNodeRefIO (Operator '+' a1 b)
  root' <- newNodeRefIO (Operator '*' partial a2)
  (_, root, _) <- atomically do createDup 1 root'
  result <- evaluate mempty root
  pure (result == IntegerValue ((a' + b') * a'))

prop_fib :: Nat -> Property
prop_fib i = monadicIO $ run do
  let fibName = 0x0
      fibF =
        [ ([IntegerValue 0], const (newNodeRef (IntegerValue 1))),
          ([IntegerValue 1], const (newNodeRef (IntegerValue 1))),
          ( [Variable Nothing],
            \(head -> n) -> do
              (_, n1, n2) <- createDup 0x1 n
              n1' <-
                newNodeRef . Operator '-' n1
                  =<< newNodeRef (IntegerValue 1)
              n2' <-
                newNodeRef . Operator '-' n2
                  =<< newNodeRef (IntegerValue 2)
              a <- newNodeRef (Constructor fibName [n1'])
              b <- newNodeRef (Constructor fibName [n2'])
              newNodeRef (Operator '+' a b)
          )
        ]
  iNode <- newNodeRefIO (IntegerValue (fromEnum i))
  root <- newNodeRefIO (Constructor fibName [iNode])
  result <- evaluate (singleton fibName fibF) root
  let expected = IntegerValue (fib (fromEnum i))
  pure (result == expected)
  where
    fib = (fibs !!)
    fibs = 1 : scanl (+) 1 fibs
