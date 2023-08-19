module Tests where

import Data.Bits
import Data.Foldable
import Data.Functor
import Data.IntMap.Strict
import GHC.Conc
import GHC.TypeLits
import Parser
import Runtime (Patterns, evaluate)
import System.Random (randomIO)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Text.Parsec (eof, runParserT)
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
  let ff =
        [ ([IntegerValue 0, Variable Nothing], pure . (!! 1)),
          ( [Variable Nothing, Variable Nothing],
            \case
              [m, f] -> lambdaHelper \x -> do
                m' <- newNodeRef . Operator '-' m =<< newNodeRef (IntegerValue 1)
                φ <- newNodeRef (Constructor 0x0 [m', f])
                (_, φ₁, φ₂) <- createDup 0 φ
                partial <- newNodeRef (Application φ₁ x)
                newNodeRef (Application φ₂ partial)
              _ -> undefined
          )
        ]
  m <- newNodeRefIO (IntegerValue (fromEnum n))
  finalF <- newNodeRefIO (Constructor 0x0 [m, notF])
  result <- newNodeRefIO (Application finalF true)
  evaluate (singleton 0x0 ff) result

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

-- BigInts
bigIntPresets :: Patterns
bigIntPresets =
  let any' = Variable Nothing
   in fromList
        [ -- End
          (0x0, [([], const do lambdaHelper \e -> lambdaHelper \_ -> lambdaHelper (const (pure e)))]),
          -- B0
          (0x1, [([any'], \(head -> p) -> lambdaHelper \_ -> lambdaHelper \o -> lambdaHelper (const do newNodeRef (Application o p)))]),
          -- B1
          (0x2, [([any'], \(head -> p) -> lambdaHelper \_ -> lambdaHelper \_ -> lambdaHelper \i -> do newNodeRef (Application i p))]),
          -- Inc
          ( 0x3,
            [ ( [any'],
                \(head -> n) -> lambdaHelper \ex -> lambdaHelper \ox -> lambdaHelper \ix -> do
                  part1 <- newNodeRef (Application n ex)
                  part2 <- newNodeRef (Application part1 ix)
                  i <- lambdaHelper \p -> do
                    ip <- newNodeRef (Constructor 0x3 [p])
                    newNodeRef (Application ox ip)
                  newNodeRef (Application part2 i)
              )
            ]
          ),
          -- App
          ( 0x4,
            [ ( [any', any', any'],
                \case
                  [n, f, x] -> do
                    e <- lambdaHelper \_ -> lambdaHelper pure
                    let φ h = lambdaHelper \z -> do
                          (_, f1, f2) <- createDup 0x4 h
                          part <- newNodeRef (Application f1 z)
                          newNodeRef (Application f2 part)
                    o <- lambdaHelper \p -> lambdaHelper \g -> lambdaHelper \y -> do
                      φ1 <- φ g
                      newNodeRef (Constructor 0x4 [p, φ1, y])
                    i <- lambdaHelper \p -> lambdaHelper \g -> lambdaHelper \y -> do
                      (_, g1, g2) <- createDup 0x4 g
                      φ1 <- φ g1
                      gy <- newNodeRef (Application g2 y)
                      newNodeRef (Constructor 0x4 [p, φ1, gy])
                    newNodeRef (Application n e)
                      >>= newNodeRef . flip Application o
                      >>= newNodeRef . flip Application i
                      >>= newNodeRef . flip Application f
                      >>= newNodeRef . flip Application x
                  _ -> undefined
              )
            ]
          ),
          -- Add
          ( 0x5,
            [ ( [any', any'],
                \case
                  [a, b] -> do
                    inc <- lambdaHelper \x -> newNodeRef (Constructor 0x3 [x])
                    newNodeRef (Constructor 0x4 [a, inc, b])
                  _ -> undefined
              )
            ]
          ),
          -- FromInt
          ( 0x6,
            [ ([IntegerValue 0], const (newNodeRef (Constructor 0x0 []))),
              ( [any'],
                \case
                  [s, i] -> do
                    one <- newNodeRef (IntegerValue 1)
                    (_, two1, two2) <-
                      createDup 0x6
                        =<< newNodeRef (IntegerValue 2)
                    (_, i1, i2) <- createDup 0x6 i
                    s1 <- newNodeRef (Operator '-' s one)
                    bit' <- newNodeRef (Operator '%' i1 two1)
                    rest <- newNodeRef (Operator '/' i2 two2)
                    newNodeRef (Constructor 0x7 [bit', s1, rest])
                  _ -> undefined
              )
            ]
          ),
          -- FromIntUtil
          ( 0x7,
            [ ( [IntegerValue 0, any', any'],
                \case
                  [_, s, i] ->
                    newNodeRef . Constructor 0x1 . pure
                      =<< newNodeRef (Constructor 0x6 [s, i])
                  _ -> undefined
              ),
              ( [IntegerValue 1, any', any'],
                \case
                  [_, s, i] ->
                    newNodeRef . Constructor 0x2 . pure
                      =<< newNodeRef (Constructor 0x6 [s, i])
                  _ -> undefined
              ),
              ([any', any', any'], error "here")
            ]
          ),
          -- ToInt
          ( 0x8,
            [ ( [any'],
                \(head -> n) -> do
                  e <- newNodeRef (IntegerValue 0)
                  one <- newNodeRef (IntegerValue 1)
                  (_, two1, two2) <- createDup 0x8 =<< newNodeRef (IntegerValue 2)
                  o <- lambdaHelper \p ->
                    newNodeRef . Operator '*' two1
                      =<< newNodeRef (Constructor 0x8 [p])
                  i <- lambdaHelper \p ->
                    newNodeRef . Operator '+' one
                      =<< newNodeRef . Operator '*' two2
                      =<< newNodeRef (Constructor 0x8 [p])
                  newNodeRef (Application n e)
                    >>= newNodeRef . flip Application o
                    >>= newNodeRef . flip Application i
              )
            ]
          ),
          -- FIXME(Maxime): output has fixed size
          ( 0x9,
            [ ( [any', any'],
                \case
                  [a, b] -> do
                    (_, b₁, b') <- createDup 0 b
                    (_, b₂, b₃) <- createDup 1 b'
                    e <- newNodeRef (Constructor 0x0 [])
                    o <- lambdaHelper \p -> do
                      rest <- newNodeRef (Constructor 0x9 [p, b₁])
                      newNodeRef (Constructor 0x1 [rest])
                    i <- lambdaHelper \p -> do
                      rest <- newNodeRef (Constructor 0x9 [p, b₂])
                      rest' <- newNodeRef (Constructor 0x1 [rest])
                      newNodeRef (Constructor 0x5 [rest', b₃])
                    newNodeRef (Application a e)
                      >>= newNodeRef . flip Application o
                      >>= newNodeRef . flip Application i
                  _ -> undefined
              )
            ]
          )
        ]

prop_bigint_iso :: Nat -> Property
prop_bigint_iso n = monadicIO $ run do
  let expected = IntegerValue (fromEnum n)
  input <- newNodeRefIO expected
  size' <- newNodeRefIO (IntegerValue (finiteBitSize @Int 0))
  scott <- newNodeRefIO (Constructor 0x6 [size', input])
  unscott <- newNodeRefIO (Constructor 0x8 [scott])
  result <- evaluate bigIntPresets unscott
  pure (result == expected)

prop_bigint_add :: Nat -> Nat -> IO Bool
prop_bigint_add a b = do
  let expected = IntegerValue (fromEnum (a + b))
  (_, size'1, size'2) <- atomically do
    createDup 0x0 =<< newNodeRef (IntegerValue (finiteBitSize @Int 0 * 2))
  a' <- newNodeRefIO (IntegerValue (fromEnum a))
  b' <- newNodeRefIO (IntegerValue (fromEnum b))
  scottA <- newNodeRefIO (Constructor 0x6 [size'1, a'])
  scottB <- newNodeRefIO (Constructor 0x6 [size'2, b'])
  scottC <- newNodeRefIO (Constructor 0x5 [scottA, scottB])
  root <- newNodeRefIO (Constructor 0x8 [scottC])
  result <- evaluate bigIntPresets root
  pure (result == expected)

prop_bigint_mul :: Nat -> Nat -> IO Bool
prop_bigint_mul a b = do
  let expected = IntegerValue (fromEnum (a * b))
  (_, size'1, size'2) <- atomically do
    createDup 0x0 =<< newNodeRef (IntegerValue (finiteBitSize @Int 0 * 2))
  a' <- newNodeRefIO (IntegerValue (fromEnum a))
  b' <- newNodeRefIO (IntegerValue (fromEnum b))
  scottA <- newNodeRefIO (Constructor 0x6 [size'1, a'])
  scottB <- newNodeRefIO (Constructor 0x6 [size'2, b'])
  scottC <- newNodeRefIO (Constructor 0x9 [scottA, scottB])
  root <- newNodeRefIO (Constructor 0x8 [scottC])
  result <- evaluate bigIntPresets root
  pure (result == expected)

prop_should_parse :: Parser a -> String -> IO Bool
prop_should_parse p s =
  atomically (runParserT (p <* eof) startScope "test" s) <&> \case
    Left _ -> False
    Right _ -> True

prop_parse_and_run :: String -> String -> IO Node
prop_parse_and_run pat src = do
  pat' <- atomically (runParserT (pattern <* eof) startScope "test" pat)
  src' <- atomically (runParserT (expr <* eof) startScope "test" src)
  case (pat', src') of
    (Right patterns, Right ref) -> evaluate patterns ref
    _ -> error "No Parse !"

prop_parse_and_check :: String -> String -> (Node -> Bool) -> IO Bool
prop_parse_and_check pat src predicate = predicate <$> prop_parse_and_run pat src
