{-# LANGUAGE ImportQualifiedPost #-}

module Main where

import GHC.TypeLits
import Parser qualified
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.Tasty.Bench
import Test.Tasty.QuickCheck
import Tests
import Types

main :: IO ()
main =
  defaultMain
    [ testProperty "tautology" prop_vie_est_belle,
      bgroup
        "parsing"
        [ testProperties "basic expressions" $
            fmap (monadicIO . run . prop_should_parse Parser.expr)
              <$> [ ("num literal", "1"),
                    ("constructor", "Hello 1 2 3"),
                    ("application", "hi 1 2 y"),
                    ("parentheses", "a b (test 1 2 3)"),
                    ("parentheses", "(test 1 2) a"),
                    ("nesting app", "hi (hello world) (And (you nesting))"),
                    ("let binding", "let a = 2, 3"),
                    ("dup binding", "dup a b = 1, 3"),
                    ("lam binding", "λx λy f x y"),
                    ("prefixbinop", "+ 1 (* 2 (/ 3 4))")
                  ],
          testProperties "patterns" $
            fmap (monadicIO . run . prop_should_parse Parser.pattern)
              <$> [ ("single name", "X = 0"),
                    ("single argument", "X a = a"),
                    ("many arguments", "X a b = a"),
                    ("many cases", "X 0 b = 1, c d = d"),
                    ("many patterns", "X 0 b = 1, c d = d. Y a = a")
                  ],
          testProperties "runs straightforward expressions" $
            let uncurry' f (a, b) = f "" a b
             in fmap (monadicIO . run . uncurry' prop_parse_and_check)
                  <$> [ ("literal", ("3", (== IntegerValue 3))),
                        ("let binding", ("let x = 3, x", (== IntegerValue 3))),
                        ("dup binding", ("dup x y = + 3 3, * x y", (== IntegerValue 36))),
                        ("identity", ("let id = λx x, id 3", (== IntegerValue 3))),
                        ("true", ("dup true t = λx λy x, true 3 4", (== IntegerValue 3))),
                        ( "not",
                          ( "dup true t = λx λy x,"
                              <> "let not = λp λx λy p y x, (not true) 3 4",
                            (== IntegerValue 4)
                          )
                        )
                      ],
          testProperties "call destructor patterns" $
            let uncurry3 f (a, b, c) = f a b c
             in fmap (monadicIO . run . uncurry3 prop_parse_and_check)
                  <$> [ ("literal", ("X = 3", "X", (== IntegerValue 3))),
                        ("simple rewrite", ("F x = + x 1", "F 3", (== IntegerValue 4))),
                        ("many arguments", ("F a b c = + a (* b c)", "F 1 2 3", (== IntegerValue 7))),
                        ("integer arguments", ("F 0 a = a", "F 0 1", (== IntegerValue 1))),
                        ("integer arguments", ("F 0 a = a, a b = a", "F 0 1", (== IntegerValue 1))),
                        ("exact matches", ("F 1 = 0, 0 = 1", "+ (F 1) (F 0)", (== IntegerValue 1))),
                        ("mixed matches", ("F 0 = 0, a = a", "F 18", (== IntegerValue 18))),
                        ("recursive identity", ("F 0 = 0, n = + 1 (F (- n 1))", "F 18", (== IntegerValue 18))),
                        ("fibonacci", ("F 0 = 1, 1 = 1, n = + (F (- n 1)) (F (- n 2))", "F 8", (== IntegerValue 34)))
                      ]
        ],
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
            ],
          bgroup
            "constructors"
            [ testProperty
                "fib function"
                ( \n -> n >= 0 && n <= 20 ==> prop_fib (toEnum n)
                )
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
              i <- [0, 8 .. 64]
              pure $ bench (show @Nat (2 ^ i)) $ nfAppIO prop_not_composition i
        ],
      bgroup
        "bigint (Scott)"
        [ testProperty
            "fromInt & toInt reciprocal correctness"
            \n -> n >= 0 ==> prop_bigint_iso (toEnum n),
          testProperty
            "addition correctness"
            \a b -> a >= 0 && b >= 0 ==> (((monadicIO . run) .) . prop_bigint_add) (toEnum a) (toEnum b),
          bgroup
            "addition scaling"
            do
              i <- [0 :: Nat, 3 .. 24]
              let n = 2 ^ i
              pure $
                bench (show @Nat n) $
                  nfAppIO (\a -> prop_bigint_add a a) n,
          bgroup
            "multiplication scaling"
            do
              i <- [0 :: Nat, 3 .. 24]
              let n = 2 ^ i
              pure $
                bench (show @Nat n) $
                  nfAppIO (\a -> prop_bigint_mul a a) n
        ]
    ]
