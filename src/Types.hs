module Types where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- Types to represent factor nodes, variable nodes, edges, and graphs:
newtype Factor = Factor String
  deriving (Show, Eq, Ord)

newtype Variable = Variable String
  deriving (Show, Eq, Ord)

type FGEdge = (Factor, Variable)

type DAGEdge = (Variable, Variable)

data DAG = DAG {
    dagVariables :: Map Variable (Set Factor)
  , dagEdges :: Set DAGEdge
  } deriving (Show, Eq, Ord)

data FactorGraph = FactorGraph {
    fgFactors :: Set Factor
  , fgVariables :: Set Variable
  , fgEdges :: Set FGEdge
  } deriving Show
