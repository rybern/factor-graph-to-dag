module Contract where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Utils
import Types

contract :: FactorGraph -> Set FGEdge -> DAG
contract (FactorGraph {fgVariables = vars, fgEdges = fgEdges}) s =
  DAG dagVars dagEdges
  where parentsF f = unionMap (\(f', v) -> if f == f' then Set.singleton v else Set.empty) (fgEdges `Set.difference` s)
        pairedV v = unionMap (\(f, v') -> if v == v' then Set.singleton f else Set.empty) s
        incomingV v =
          let paired = pairedV v in
            ((v, paired), Set.map (\v' -> (v', v)) $ unionMap parentsF paired)
        results = Set.map incomingV vars
        dagVars = Set.fold (\((v, fs), _) m -> Map.insert v fs m) Map.empty results
        dagEdges = unionMap snd results

