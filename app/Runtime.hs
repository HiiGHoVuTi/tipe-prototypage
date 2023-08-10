module Runtime where

import Control.Monad
import Data.Bitraversable
import Data.Functor
import Data.IntMap.Strict
import Data.Maybe
import GHC.Conc
import System.Random (randomIO)
import Types

type Patterns = IntMap [([Node], [NodeRef] -> STM NodeRef)]

evaluate :: Patterns -> NodeRef -> IO Node
evaluate pat = evaluate'
  where
    evaluate' root =
      readNodeRefIO root >>= \case
        Variable (Just α) -> evaluate' α
        Duplicated ρ -> do
          Duplication ι v (δ₁, δ₂) <- readNodeRefIO ρ
          -- NOTE(Maxime): avoid extra work, evaluate' once
          β <- evaluate' v
          atomically do writeNodeRef v β
          unless (root `elem` [δ₁, δ₂]) (error "INCOHERENT")
          case β of
            Constructor μ xs ->
              atomically do
                (_, δ₁s, δ₂s) <- unzip3 <$> traverse (createDup ι) xs
                writeNodeRef δ₁ (Constructor μ δ₁s)
                writeNodeRef δ₂ (Constructor μ δ₂s)
                *> evaluate' root
            Lambda arg body ->
              atomically do
                arg'₁ <- newNodeRef (Variable Nothing)
                arg'₂ <- newNodeRef (Variable Nothing)
                (_, body'₁, body'₂) <- createDup ι body
                σ <- newNodeRef (Superposition ι (arg'₁, arg'₂))
                writeNodeRef arg (Variable (Just σ))
                writeNodeRef δ₁ (Lambda arg'₁ body'₁)
                writeNodeRef δ₂ (Lambda arg'₂ body'₂)
                *> evaluate' root
            Superposition ι' (σ₁, σ₂)
              | ι == ι' -> do
                  atomically do
                    writeNodeRef δ₁ =<< readNodeRef σ₁
                    writeNodeRef δ₂ =<< readNodeRef σ₂
                    *> evaluate' root
              | otherwise -> do
                  (ι₁, ι₂) <- bisequence (randomIO, randomIO)
                  atomically do
                    (_, δ₁σ₁, δ₂σ₁) <- createDup ι₁ σ₁
                    (_, δ₁σ₂, δ₂σ₂) <- createDup ι₂ σ₂
                    writeNodeRef δ₁ (Superposition ι₁ (δ₁σ₁, δ₁σ₂))
                    writeNodeRef δ₂ (Superposition ι₂ (δ₂σ₁, δ₂σ₂))
                  evaluate' root
            n@IntegerValue {} -> do
              atomically do
                writeNodeRef δ₁ n
                writeNodeRef δ₂ n
                *> evaluate' root
            -- NOTE(Maxime): already in nf
            _ -> error "invariant broken"
        Application φ α ->
          readNodeRefIO φ >>= \case
            Lambda arg body ->
              atomically do
                writeNodeRef arg (Variable (Just α))
                *> evaluate' body
            Superposition ι (σ₁, σ₂) ->
              atomically do
                (_, α₁, α₂) <- createDup ι α
                σ₁' <- newNodeRef (Application σ₁ α₁)
                σ₂' <- newNodeRef (Application σ₂ α₂)
                writeNodeRef root (Superposition ι (σ₁', σ₂'))
                *> evaluate' root
            f -> do
              ψ <- evaluate' φ
              atomically do writeNodeRef φ ψ
              -- TODO(Maxime): avoid this using a whnf detector
              when (f == ψ) (error ("impossible to evaluate' " <> showNode f))
              evaluate' root
        Operator c x y -> do
          Just op <- pure $ Prelude.lookup c [('+', (+)), ('-', (-)), ('*', (*)), ('/', quot), ('%', rem)]
          (,) <$> evaluate' x <*> evaluate' y >>= \case
            (IntegerValue a, IntegerValue b) -> pure (IntegerValue (a `op` b))
            _ -> error "called operator on non-integers"
        Constructor ι xs
          | ι `member` pat ->
              do
                let matches _ (Variable Nothing) = pure (Just ())
                    matches x' y = do
                      x <- evaluate' x'
                      pure (guard (x == y))
                    matchAndGenerate (ys, pattern) = do
                      match <-
                        Prelude.foldl (*>) (Just ())
                          <$> zipWithM matches xs ys
                      pure (match $> pattern xs)
                newRef <-
                  fmap (head . catMaybes)
                    . mapM matchAndGenerate
                    $ pat ! ι
                atomically (writeNodeRef root =<< readNodeRef =<< newRef)
                *> evaluate' root
        node -> pure node
