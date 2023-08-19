module Parser where

import Control.Monad
import Control.Monad.Trans
import Data.Char
import Data.Foldable
import Data.Functor
import Data.Hashable
import Data.Map
import GHC.Conc
import GHC.Generics
import Text.Parsec
import Types

data Scope = Scope {scope :: Map String NodeRef, iotas :: [Identifier]}
  deriving (Generic)

startScope :: Scope
startScope = Scope mempty [0 ..]

modifyScope :: (Map String NodeRef -> Map String NodeRef) -> Scope -> Scope
modifyScope f s = s {scope = f (scope s)}

modifyIotas :: ([Identifier] -> [Identifier]) -> Scope -> Scope
modifyIotas f s = s {iotas = f (iotas s)}

type Parser = ParsecT String Scope STM

identifierChars :: [Char]
identifierChars = ['a' .. 'z']

(.:) :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
(.:) = (.) . (.)

expr :: Parser NodeRef
expr = expr'List <|> expr'
  where
    letParser = try do
      spaces
      void (string "let")
      spaces
      name <- many1 (oneOf identifierChars)
      spaces
      void (string "=")
      spaces
      value <- expr
      spaces
      modifyState (modifyScope (insert name value))
      void (string "in")
      spaces
      expr
    dupParser = try do
      spaces
      void (string "dup")
      spaces
      name1 <- many1 (oneOf identifierChars)
      spaces
      name2 <- many1 (oneOf identifierChars)
      spaces
      void (string "=")
      spaces
      value <- expr
      spaces
      iota <- getState <&> iotas <&> head
      modifyState (modifyIotas tail)
      (_, δ₁, δ₂) <- lift (createDup iota value)
      modifyState (modifyScope (insert name2 δ₂ . insert name1 δ₁))
      void (string "in")
      spaces
      expr
    exprParen = spaces *> char '(' *> expr' <* char ')' <* spaces
    integer = try do
      spaces
      i <- read @Int <$> many1 (oneOf ['0' .. '9'])
      spaces
      lift (newNodeRef (IntegerValue i))
    identifier = try do
      spaces
      name <- many1 (oneOf identifierChars)
      spaces
      getState <&> scope <&> (! name)
    expr'List = try do
      spaces
      (x : xs) <- many1 expr'
      spaces
      foldlM ((lift . newNodeRef) .: Application) x xs
    constructor = try do
      spaces
      name <- hash .: (:) <$> oneOf (toUpper <$> identifierChars) <*> many (oneOf identifierChars)
      spaces
      arguments <- many expr
      lift (newNodeRef (Constructor name arguments))
    expr' =
      exprParen
        <|> integer
        <|> letParser
        <|> dupParser
        <|> constructor
        <|> identifier
