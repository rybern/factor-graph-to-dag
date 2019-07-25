module Main where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import SAT.MiniSat hiding (Formula)
import qualified SAT.MiniSat (Formula)

-- Types to represent factor nodes, variable nodes, edges, and graphs:
newtype Factor = Factor String
  deriving (Show, Eq, Ord)

newtype Variable = Variable String
  deriving (Show, Eq, Ord)

type Edge = (Factor, Variable)

data FactorGraph = FactorGraph {
    factors :: Set Factor
  , variables :: Set Variable
  , edges :: Set Edge
}

-- The atomic propositions we need:
data Prop =
  -- A factor has a path to a variable
    ReachesV Factor Variable
  -- A factor has a path to a factor
  | ReachesF Factor Factor
  -- An edge is selected to be in the cover
  | Selected Factor Variable
          deriving (Eq, Ord, Show)

type Formula = SAT.MiniSat.Formula Prop

-- Helpers to operate with sets and predicates
exactlyOne' :: (a -> Formula) -> Set a -> Formula
exactlyOne' f = ExactlyOne . Set.toList . Set.map f

atMostOne' :: (a -> Formula) -> Set a -> Formula
atMostOne' f = AtMostOne . Set.toList . Set.map f

all' :: (a -> Formula) -> Set a -> Formula
all' f = All . Set.toList . Set.map f

-- Construct the proposition meaning an edge is selected as part of the cover set
select :: Edge -> Formula
select (f, v) = Var (Selected f v)

-- Construct the proposition meaning "There is a path from factor f to variable v"
reachesVariable :: Factor -> Variable -> Formula
reachesVariable f v = Var (ReachesV f v)

-- Construct the proposition meaning "There is a path from factor f1 to factor f2"
reachesFactor :: Factor -> Factor -> Formula
reachesFactor f1 f2 = Var (ReachesF f1 f2)

-- Get the subset of edges involving a variable
variableEdges :: FactorGraph -> Variable -> Set Edge
variableEdges g v = Set.filter (\(_, v') -> v' == v) (edges g)

-- Get the subset of edges involving a factor
factorEdges :: FactorGraph -> Factor -> Set Edge
factorEdges g f = Set.filter (\(f', _) -> f' == f) (edges g)

-- A factor is the sampling statement for exactly one variable
oneSelected :: Set Edge -> Formula
oneSelected =
  exactlyOne' select

-- A variable has no more than one sampling statement
atMostOneSelected :: Set Edge -> Formula
atMostOneSelected =
  atMostOne' select

-- If an edge is assigned and its factor is reachable,
-- then its variable is reachable
assignedReachable :: Set Factor -> Edge -> Formula
assignedReachable fs e@(f, v) =
  (select e :->: reachesVariable f v) :&&:
  (all' (\f' -> select e :&&: reachesFactor f' f :->: reachesVariable f' v) fs)

-- If an edge is unassigned and its variable is reachable,
-- then its factor is reachable
unassignedReachable :: Set Factor -> Edge -> Formula
unassignedReachable fs e@(f, v) =
  all' (\f' -> (Not (select e) :&&: reachesVariable f' v) :->: reachesFactor f' f) fs

-- No factor has a path to itself
noCycles :: Set Factor -> Formula
noCycles = all' (\f -> Not (reachesFactor f f))

{- A graph has an acyclic edge cover if:
  * It has no cycles under its interpretation as a directed graph
  * Each factor is assigned to one variable,
  * Each variable is assigned to at most one factor
-}
acyclicEdgeCoverFormula :: FactorGraph -> Formula
acyclicEdgeCoverFormula g =
  noCycles (factors g)
  :&&: all' factorwiseFormula (factors g)
  :&&: all' variablewiseFormula (variables g)
  where factorwiseFormula f =
          let edges = factorEdges g f
          in oneSelected edges
             :&&: all' (assignedReachable fs) edges
             :&&: all' (unassignedReachable fs) edges
        variablewiseFormula v =
          atMostOneSelected (variableEdges g v)
        fs = factors g

-- The SAT solver returns a map assigning each Prop to a Bool.
-- Extract a the set of edges assigned in the cover.
parseCover :: Map Prop Bool -> Set Edge
parseCover = Set.fromList . Map.elems . Map.mapMaybeWithKey getTrueEdge
  where getTrueEdge (Selected f v) True = Just (f, v)
        getTrueEdge _ _ = Nothing

-- Use the SAT solver to find covering sets for a graph
findCovers :: FactorGraph -> [Set Edge]
findCovers = nub . map parseCover . solve_all . acyclicEdgeCoverFormula
  where nub = Set.toList . Set.fromList -- removes duplicates

-- Example factor graph with a cycle: it would be invalid to assign B--b.
example1 :: FactorGraph
example1 = FactorGraph {
    factors = Set.fromList . map Factor $ ["A", "B"]
  , variables = Set.fromList . map Variable $ ["a", "b", "c"]
  , edges = Set.fromList [
        (Factor "A", Variable "a")
      , (Factor "A", Variable "b")
      , (Factor "B", Variable "a")
      , (Factor "B", Variable "b")
      , (Factor "B", Variable "c")
      ]
  }

main :: IO ()
main = do
  mapM_ print $ findCovers example1
{-
output:

  {(Factor "A",Variable "a"), (Factor "B",Variable "c")}
  {(Factor "A",Variable "b"), (Factor "B",Variable "c")}
-}


-- Example factor graph with no solution
example2 :: FactorGraph
example2 = FactorGraph {
    factors = Set.fromList . map Factor $ ["A", "B"]
  , variables = Set.fromList . map Variable $ ["a", "b"]
  , edges = Set.fromList [
        (Factor "A", Variable "a")
      , (Factor "A", Variable "b")
      , (Factor "B", Variable "a")
      , (Factor "B", Variable "b")
      ]
  }
-- output: []

{-
Stan eight-schools:
data {
  int<lower=0> J;          // number of schools
  real y[J];               // estimated treatment effect (school j)
  real<lower=0> sigma[J];  // std err of effect estimate (school j)
}
parameters {
  real mu;
  real theta[J];
  real<lower=0> tau;
}
model {
  theta ~ normal(mu, tau);
  y ~ normal(theta,sigma);
}

-}

-- Example factor graph of eight-schools
example3 :: FactorGraph
example3 = FactorGraph {
    factors = Set.fromList . map Factor $ ["theta ~ normal(mu, tau)", "y ~ normal(theta,sigma)"]
  , variables = Set.fromList . map Variable $ ["mu", "theta", "tau", "J", "y", "sigma"]
  , edges = Set.fromList [
        (Factor "theta ~ normal(mu, tau)", Variable "mu")
      , (Factor "theta ~ normal(mu, tau)", Variable "tau")
      , (Factor "theta ~ normal(mu, tau)", Variable "theta")
      , (Factor "y ~ normal(theta,sigma)", Variable "theta")
      , (Factor "y ~ normal(theta,sigma)", Variable "sigma")
      , (Factor "y ~ normal(theta,sigma)", Variable "y")
      ]
  }
{- output:
  {(Factor "theta ~ normal(mu, tau)",Variable "mu"),(Factor "y ~ normal(theta,sigma)",Variable "theta")}
  {(Factor "theta ~ normal(mu, tau)",Variable "mu"),(Factor "y ~ normal(theta,sigma)",Variable "y")}
  {(Factor "theta ~ normal(mu, tau)",Variable "tau"),(Factor "y ~ normal(theta,sigma)",Variable "sigma")}
  {(Factor "theta ~ normal(mu, tau)",Variable "tau"),(Factor "y ~ normal(theta,sigma)",Variable "theta")}
  {(Factor "theta ~ normal(mu, tau)",Variable "tau"),(Factor "y ~ normal(theta,sigma)",Variable "y")}
  {(Factor "theta ~ normal(mu, tau)",Variable "theta"),(Factor "y ~ normal(theta,sigma)",Variable "sigma")}
  {(Factor "theta ~ normal(mu, tau)",Variable "theta"),(Factor "y ~ normal(theta,sigma)",Variable "y")}
-}

