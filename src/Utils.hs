module Utils where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe

unionMap :: Ord b => (a -> Set b) -> Set a -> Set b
unionMap f = Set.fold Set.union Set.empty . Set.map f

setMapMaybe :: Ord b => (a -> Maybe b) -> Set a -> Set b
setMapMaybe f = Set.map fromJust . Set.filter isJust . Set.map f
