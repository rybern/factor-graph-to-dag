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

-- Example factor graph with a cycle: it would be invalid to assign B--b.
example1 :: FactorGraph
example1 = FactorGraph {
    fgFactors = Set.fromList . map Factor $ ["A", "B"]
  , fgVariables = Set.fromList . map Variable $ ["a", "b", "c"]
  , fgEdges = Set.fromList [
        (Factor "A", Variable "a")
      , (Factor "A", Variable "b")
      , (Factor "B", Variable "a")
      , (Factor "B", Variable "b")
      , (Factor "B", Variable "c")
      ]
  }

{-
output:

  {(Factor "A",Variable "a"), (Factor "B",Variable "c")}
  {(Factor "A",Variable "b"), (Factor "B",Variable "c")}
-}


-- Example factor graph with no solution
example2 :: FactorGraph
example2 = FactorGraph {
    fgFactors = Set.fromList . map Factor $ ["A", "B"]
  , fgVariables = Set.fromList . map Variable $ ["a", "b"]
  , fgEdges = Set.fromList [
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
-- Note: this isn't actually produced from the stanc3 factor graph code, because it doesn't yet emit data variables
example3 :: FactorGraph
example3 = FactorGraph {
    fgFactors = Set.fromList . map Factor $ ["theta ~ normal(mu, tau)", "y ~ normal(theta,sigma)"]
  , fgVariables = Set.fromList . map Variable $ vs
  , fgEdges = unis <> Set.fromList [
        (Factor "theta ~ normal(mu, tau)", Variable "mu")
      , (Factor "theta ~ normal(mu, tau)", Variable "tau")
      , (Factor "theta ~ normal(mu, tau)", Variable "theta")
      , (Factor "y ~ normal(theta,sigma)", Variable "theta")
      , (Factor "y ~ normal(theta,sigma)", Variable "sigma")
      , (Factor "y ~ normal(theta,sigma)", Variable "y")
      ]
  }
  where vs = ["mu", "theta", "tau", "J", "y", "sigma"]
        unis = Set.fromList $ map (
          \v ->
            (Factor (v ++ " ~ UNI"), Variable v)) ["mu", "theta", "tau", "J", "y", "sigma"]
{- output:
  {(Factor "theta ~ normal(mu, tau)",Variable "mu"),(Factor "y ~ normal(theta,sigma)",Variable "theta")}
  {(Factor "theta ~ normal(mu, tau)",Variable "mu"),(Factor "y ~ normal(theta,sigma)",Variable "y")}
  {(Factor "theta ~ normal(mu, tau)",Variable "tau"),(Factor "y ~ normal(theta,sigma)",Variable "sigma")}
  {(Factor "theta ~ normal(mu, tau)",Variable "tau"),(Factor "y ~ normal(theta,sigma)",Variable "theta")}
  {(Factor "theta ~ normal(mu, tau)",Variable "tau"),(Factor "y ~ normal(theta,sigma)",Variable "y")}
  {(Factor "theta ~ normal(mu, tau)",Variable "theta"),(Factor "y ~ normal(theta,sigma)",Variable "sigma")}
  {(Factor "theta ~ normal(mu, tau)",Variable "theta"),(Factor "y ~ normal(theta,sigma)",Variable "y")}
-}


-- Example factor graph of eight-schools
-- Note: this isn't actually produced from the stanc3 factor graph code, because it doesn't yet emit data variables
{-

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
  target += normal_lpdf(mu | 1, 1);
  target += normal_lpdf(tau | 1, 1);
  target += normal_lpdf(theta | mu, tau);
  target += normal_lpdf(y | theta, sigma);
}


graph {
  "normal_lpdf(y, theta, sigma)" [shape=box]
  "normal_lpdf(theta, mu, tau)" [shape=box]
  "normal_lpdf(tau, 1, 1)" [shape=box]
  "normal_lpdf(mu, 1, 1)" [shape=box]
  mu
  sigma
  tau
  theta
  y
  "normal_lpdf(y, theta, sigma)" -- sigma
  "normal_lpdf(y, theta, sigma)" -- theta
  "normal_lpdf(y, theta, sigma)" -- y
  "normal_lpdf(theta, mu, tau)" -- mu
  "normal_lpdf(theta, mu, tau)" -- tau
  "normal_lpdf(theta, mu, tau)" -- theta
  "normal_lpdf(tau, 1, 1)" -- tau
  "normal_lpdf(mu, 1, 1)" -- mu
}
-}
example4  :: Bool -> FactorGraph
example4 params = FactorGraph {
    fgFactors = Set.fromList . map Factor $
      [ "normal_lpdf(y, theta, sigma)"
      , "normal_lpdf(theta, mu, tau)"
      , "normal_lpdf(tau, 1, 1)"
      , "normal_lpdf(mu, 1, 1)"
      ]
  , fgVariables = Set.fromList . map Variable $
    if params then
      [ "mu"
      , "tau"
      , "theta"
      ]
    else
      [ "sigma"
      , "y"
      ]
  , fgEdges = Set.fromList $
    if params then
      [ (Factor "normal_lpdf(y, theta, sigma)", Variable "theta")
      , (Factor "normal_lpdf(theta, mu, tau)", Variable "mu")
      , (Factor "normal_lpdf(theta, mu, tau)", Variable "tau")
      , (Factor "normal_lpdf(theta, mu, tau)", Variable "theta")
      , (Factor "normal_lpdf(tau, 1, 1)", Variable "tau")
      , (Factor "normal_lpdf(mu, 1, 1)", Variable "mu")
      ]
    else
      [ (Factor "normal_lpdf(y, theta, sigma)", Variable "sigma")
      , (Factor "normal_lpdf(y, theta, sigma)", Variable "y")
      ]
  }
  where unis = Set.fromList $ map (
          \v ->
            (Factor (v ++ " ~ UNI"), Variable v)) ["mu", "theta", "tau", "y", "sigma"]
{- output:
  {(Factor "theta ~ normal(mu, tau)",Variable "mu"),(Factor "y ~ normal(theta,sigma)",Variable "theta")}
  {(Factor "theta ~ normal(mu, tau)",Variable "mu"),(Factor "y ~ normal(theta,sigma)",Variable "y")}
  {(Factor "theta ~ normal(mu, tau)",Variable "tau"),(Factor "y ~ normal(theta,sigma)",Variable "sigma")}
  {(Factor "theta ~ normal(mu, tau)",Variable "tau"),(Factor "y ~ normal(theta,sigma)",Variable "theta")}
  {(Factor "theta ~ normal(mu, tau)",Variable "tau"),(Factor "y ~ normal(theta,sigma)",Variable "y")}
  {(Factor "theta ~ normal(mu, tau)",Variable "theta"),(Factor "y ~ normal(theta,sigma)",Variable "sigma")}
  {(Factor "theta ~ normal(mu, tau)",Variable "theta"),(Factor "y ~ normal(theta,sigma)",Variable "y")}
-}
