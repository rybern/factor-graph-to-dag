module Main where

import System.Environment (getArgs)

import SATSolve
import Types
import Contract
import Query
import Recognize

import qualified Data.Sequence as Seq
import Data.Foldable (toList)
import Control.Monad
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import SAT.MiniSat hiding (Formula)
import qualified SAT.MiniSat (Formula)

import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as T
import Data.Text (Text)

import Data.GraphViz.Types
import Data.GraphViz.Parsing
import Data.GraphViz.Types.Generalised
import Data.GraphViz.Attributes.Complete

main :: IO ()
main = do
  [inFile, outFile] <- getArgs
  inContent <- T.readFile inFile
  let fg = parseFG . parseIt' $ inContent
      r = recognizeSet fg
      edgeSelectionSets = findCovers r fg
      dags = map (contract fg) edgeSelectionSets
  maybeDag <- queryFilterAll (Set.map snd r) $ Set.fromList dags
  case maybeDag of
    Just dag -> do
      T.writeFile outFile . printDotGraph . mapDotGraph T.pack . dagToDot $ dag
      putStrLn "DAG successfully produced."
    Nothing ->
      putStrLn "No DAG could be produced."




parseNode :: DotStatement String -> Maybe (DotNode String)
parseNode (DN n) = Just n
parseNode _ = Nothing

parseEdge :: (DotStatement String) -> Maybe (DotEdge String)
parseEdge (DE n) = Just n
parseEdge _ = Nothing

parseFGF :: (DotNode String) -> Maybe Factor
parseFGF (DotNode s attr)
  | Shape BoxShape `elem` attr = Just (Factor s)
  | otherwise = Nothing

parseFGV :: (DotNode String) -> Maybe Variable
parseFGV (DotNode s attr)
  | Shape BoxShape `notElem` attr = Just (Variable s)
  | otherwise = Nothing

parseFGE :: Set Factor -> Set Variable -> (DotEdge String) -> (Factor, Variable)
parseFGE factors variables (DotEdge f v _)
  | Factor f `Set.notMember` factors = error $ "Factor not found: " ++ f ++ " in set: " ++ show factors
  | Variable v `Set.notMember` variables = error $ "Variable not found: " ++ v
  | otherwise = (Factor f, Variable v)

parseFG :: (DotGraph String) -> FactorGraph
parseFG (DotGraph {directedGraph = False, graphStatements = stmts}) =
  FactorGraph factors variables edges
  where parseStmts p = Set.fromList . mapMaybe p . toList $ stmts
        parseNodes p = parseStmts (parseNode >=> p)
        parseEdges p = parseStmts (parseEdge >=> p)
        factors = parseNodes parseFGF
        variables = parseNodes parseFGV
        edges = parseEdges (Just . parseFGE factors variables)
parseFG _ = error "Tried to interpret directed graph as factor graph"

dagEdgeEdge :: DAGEdge -> DotEdge String
dagEdgeEdge (Variable v1, Variable v2) = DotEdge v1 v2 []

dagVarNode :: Variable -> (Set Factor) -> DotNode String
dagVarNode (Variable v) _  = DotNode v []

dagEdgeStmts :: Set DAGEdge -> DotStatements String
dagEdgeStmts = Seq.fromList . Set.toList . Set.map (DE . dagEdgeEdge)

dagVarStmts :: Map Variable (Set Factor) -> DotStatements String
dagVarStmts = Seq.fromList . map (DN . uncurry dagVarNode) . Map.toList

dagToDot :: DAG -> DotGraph String
dagToDot (DAG vars edges) =
  DotGraph {
    directedGraph = True
  , strictGraph = True
  , graphID = Nothing
  , graphStatements =
      dagVarStmts vars <> dagEdgeStmts edges
  }
