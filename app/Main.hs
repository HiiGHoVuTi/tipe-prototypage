{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad
import GHC.Conc
import System.Exit (exitFailure)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import System.Random (randomIO)
import Data.Bitraversable

-- types

type Identifier = Word

type NodeRef = TVar Node

data Node
  = Superposition Identifier (NodeRef, NodeRef)
  | Duplication Identifier NodeRef (NodeRef, NodeRef)
  | Duplicated NodeRef
  | IntegerValue Int
  | Lambda NodeRef NodeRef
  | Variable
  | Application NodeRef NodeRef
  | Constructor Identifier [NodeRef]
  deriving (Eq)

createDup :: Identifier -> NodeRef -> STM (NodeRef, NodeRef, NodeRef)
createDup ι α = do
  δ₁ <- newTVar Variable
  δ₂ <- newTVar Variable
  ρ <- newTVar (Duplication ι α (δ₁, δ₂))
  writeTVar δ₁ (Duplicated ρ)
  writeTVar δ₂ (Duplicated ρ)
  pure (ρ, δ₁, δ₂)

duplicationOf :: Node -> IO (NodeRef, NodeRef, NodeRef)
duplicationOf ν = do
  α <- newTVarIO ν
  ι <- randomIO
  atomically do createDup ι α

evaluate :: NodeRef -> IO Node
evaluate root =
  readTVarIO root >>= \case
    Duplicated ρ -> do
      Duplication ι v (δ₁, δ₂) <- readTVarIO ρ
      readTVarIO v >>= \case
        Constructor μ xs ->
          atomically do
            (_, δ₁s, δ₂s) <- unzip3 <$> traverse (createDup ι) xs
            writeTVar δ₁ (Constructor μ δ₁s)
            writeTVar δ₂ (Constructor μ δ₂s)
            *> evaluate root
        Lambda arg body ->
          atomically do
            arg'₁ <- newTVar Variable
            arg'₂ <- newTVar Variable
            (_, body'₁, body'₂) <- createDup ι body
            writeTVar arg (Superposition ι (arg'₁, arg'₂))
            writeTVar δ₁ (Lambda arg'₁ body'₁)
            writeTVar δ₂ (Lambda arg'₂ body'₂)
            *> evaluate root
        Superposition ι' (σ₁, σ₂)
          | ι == ι' ->
              atomically do
                writeTVar δ₁ =<< readTVar σ₁
                writeTVar δ₂ =<< readTVar σ₂
                *> evaluate root
          | otherwise -> do
              (ι₁, ι₂) <- bisequence (randomIO, randomIO)
              atomically do
                (_, δ₁σ₁, δ₂σ₁) <- createDup ι₁ σ₁
                (_, δ₁σ₂, δ₂σ₂) <- createDup ι₂ σ₂
                writeTVar δ₁ (Superposition ι₁ (δ₁σ₁, δ₁σ₂))
                writeTVar δ₂ (Superposition ι₂ (δ₂σ₁, δ₂σ₂))
              evaluate root
        i@(IntegerValue _) ->
          atomically do
            writeTVar δ₁ i
            writeTVar δ₂ i
            *> evaluate root
        _ -> fail "invariant broken"
    Application φ α ->
      readTVarIO φ >>= \case
        Lambda arg body ->
          atomically do
            writeTVar arg =<< readTVar α
            *> evaluate body
        Superposition ι (σ₁, σ₂) ->
          atomically do
            writeTVar σ₁ (Application φ σ₁)
            writeTVar σ₂ (Application φ σ₂)
            writeTVar root (Superposition ι (σ₁, σ₂))
            *> evaluate root
        _ -> do
          ψ <- evaluate φ
          atomically do writeTVar φ ψ
          evaluate root
    n -> pure n

-- tests

prop_vie_est_belle :: Bool
prop_vie_est_belle = True

prop_id_on_int :: Int -> Property
prop_id_on_int i = monadicIO $ run do
  let expected = IntegerValue i
  valu <- newTVarIO expected
  ldva <- newTVarIO Variable
  lmbd <- newTVarIO (Lambda ldva ldva)
  root <- newTVarIO (Application lmbd valu)
  result <- evaluate root
  pure (result == expected)

prop_dup_id :: Int -> Property
prop_dup_id i = monadicIO $ run do
  let expected = IntegerValue i
  inpu <- newTVarIO expected
  ldva <- newTVarIO Variable
  lmid <- newTVarIO (Lambda ldva ldva)
  (_, clo1, _) <- atomically do createDup 0 lmid
  root <- newTVarIO (Application clo1 inpu)
  result <- evaluate root
  pure (result == expected)

return []

main :: IO ()
main = do
  good <- $quickCheckAll
  unless good exitFailure
