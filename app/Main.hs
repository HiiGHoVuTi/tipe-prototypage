module Main where

import GHC.TypeLits
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
              i <- [0, 2 .. 64]
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
              i <- [0 :: Nat, 2 .. 16]
              let n = 2 ^ i
              pure $
                bench (show @Nat n) $
                  nfAppIO (\a -> prop_bigint_add a a) n
        ]
    ]
