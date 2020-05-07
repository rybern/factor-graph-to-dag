module Recognize where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe

import Text.Megaparsec
import Text.Megaparsec.Char

import Types

recognizeSet :: FactorGraph -> Set FGEdge
recognizeSet = Set.filter recognize . fgEdges

recognize :: FGEdge -> Bool
recognize (Factor f, Variable v) =
  case parseMaybe parseRecog f of
    Just (Recog {variate = v'}) -> v == v'
    _ -> False

testRecog = parse parseRecog ""

data Recog = Recog {
    fname :: String
  , variate :: String
  , remainder :: String
  } deriving Show

parseRecog :: Parsec () String Recog
parseRecog = do
  space
  fname <- someTill (letterChar <|> char '_') (string "_lpdf")
  space
  char '('
  variate <- someTill letterChar $ do
    space
    (char ',' <|> char '|')
  remainder <- manyTill asciiChar (char ')')
  return $ Recog fname variate remainder
