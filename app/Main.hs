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
