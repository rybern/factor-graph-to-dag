module Utils where

import Data.Set (Set)
import qualified Data.Set as Set

unionMap :: Ord b => (a -> Set b) -> Set a -> Set b
unionMap f = Set.fold Set.union Set.empty . Set.map f
