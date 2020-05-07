module SATSolve where

import System.IO

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import SAT.MiniSat hiding (Formula)
import qualified SAT.MiniSat (Formula)

import Types
import Utils

type Formula = SAT.MiniSat.Formula Prop

-- The atomic propositions we need:
data Prop =
  -- A factor has a path to a variable
    ReachesV Factor Variable
  -- A factor has a path to a factor
  | ReachesF Factor Factor
  -- An edge is selected to be in the cover
  | Selected Factor Variable
          deriving (Eq, Ord, Show)

-- Helpers to operate with sets and predicates
exactlyOne' :: (a -> Formula) -> Set a -> Formula
exactlyOne' f = ExactlyOne . Set.toList . Set.map f

atLeastOne' :: (a -> Formula) -> Set a -> Formula
atLeastOne' f = Some . Set.toList . Set.map f

atMostOne' :: (a -> Formula) -> Set a -> Formula
atMostOne' f = AtMostOne . Set.toList . Set.map f

all' :: (a -> Formula) -> Set a -> Formula
all' f = All . Set.toList . Set.map f

-- Construct the proposition meaning an edge is selected as part of the cover set
select :: FGEdge -> Formula
select (f, v) = Var (Selected f v)

-- Construct the proposition meaning "There is a path from factor f to variable v"
reachesVariable :: Factor -> Variable -> Formula
reachesVariable f v = Var (ReachesV f v)

-- Construct the proposition meaning "There is a path from factor f1 to factor f2"
reachesFactor :: Factor -> Factor -> Formula
reachesFactor f1 f2 = Var (ReachesF f1 f2)

-- Get the subset of edges involving a variable
variableEdges :: FactorGraph -> Variable -> Set FGEdge
variableEdges g v = Set.filter (\(_, v') -> v' == v) (fgEdges g)

-- Get the subset of edges involving a factor
factorEdges :: FactorGraph -> Factor -> Set FGEdge
factorEdges g f = Set.filter (\(f', _) -> f' == f) (fgEdges g)

-- If an edge is assigned and its factor is reachable,
-- then its variable is reachable
assignedReachable :: Set Factor -> FGEdge -> Formula
assignedReachable fs e@(f, v) =
  (select e :->: reachesVariable f v) :&&:
  (all' (\f' -> select e :&&: reachesFactor f' f :->: reachesVariable f' v) fs)

-- If an edge is unassigned and its variable is reachable,
-- then its factor is reachable
unassignedReachable :: Set Factor -> FGEdge -> Formula
unassignedReachable fs e@(f, v) =
  all' (\f' -> (Not (select e) :&&: reachesVariable f' v) :->: reachesFactor f' f) fs

-- No factor has a path to itself
noCycles :: Set Factor -> Formula
noCycles = all' (\f -> Not (reachesFactor f f))

{- A graph has an acyclic edge cover if:
  * It has no cycles under its interpretation as a directed graph
  * Each factor is assigned to one variable,
  * Each variable is assigned to at least one factor
-}
acyclicEdgeCoverFormula :: Set FGEdge -> FactorGraph -> Formula
acyclicEdgeCoverFormula r g =
  noCycles (fgFactors g)
  :&&: all' factorwiseFormula (fgFactors g)
  :&&: all' variablewiseFormula (fgVariables g)
  :&&: recognizedFormula r g
  where factorwiseFormula f =
          let edges = factorEdges g f
          in exactlyOne' select edges
             :&&: all' (assignedReachable fs) edges
             :&&: all' (unassignedReachable fs) edges
        variablewiseFormula v =
          atLeastOne' select (variableEdges g v)
        fs = fgFactors g

recognizedFormula :: Set FGEdge -> FactorGraph -> Formula
recognizedFormula r g =
  all' select r
  :&&: all' (Not . select) (touchedEdges `Set.difference` r)
  where coveredFactors = Set.map fst r
        touchedEdges = unionMap (factorEdges g) coveredFactors

-- The SAT solver returns a map assigning each Prop to a Bool.
-- Extract a the set of edges assigned in the cover.
parseCover :: Map Prop Bool -> Set FGEdge
parseCover = Set.fromList . Map.elems . Map.mapMaybeWithKey getTrueEdge
  where getTrueEdge (Selected f v) True = Just (f, v)
        getTrueEdge _ _ = Nothing

-- Use the SAT solver to find covering sets for a graph
findCovers :: Set FGEdge -> FactorGraph -> [Set FGEdge]
findCovers r = nub . map parseCover . solve_all . acyclicEdgeCoverFormula r
  where nub = Set.toList . Set.fromList -- removes duplicates
