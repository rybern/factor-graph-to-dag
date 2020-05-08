{-# LANGUAGE FlexibleContexts #-}
module Query where

import System.IO
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.State
import Control.Monad.State.Class
import Data.Maybe
import Data.List
import Data.Functor
import qualified Text.Read as Read

import Types
import Utils

queryFilterAll :: Set Variable -> Set DAG -> IO (Maybe DAG)
queryFilterAll ignore dags = case Set.lookupMin dags of
  Nothing -> return Nothing
  Just dag -> (Set.lookupMin <$>) . flip execStateT dags $
    let queryParams = Set.fromList . filter (`Set.notMember` ignore) . Map.keys . dagVariables $ dag
    in doWhile queryParams nextParameter queryFilterV

-- Do a monadic action on pieces of a thing, until the thing is gone
doWhile :: (Monad m) => a -> (a -> m (Maybe (b, a))) -> (b -> m ()) -> m ()
doWhile whole break act = do
  broken <- break whole
  case broken of
    Just (part, next) -> act part >> doWhile next break act
    Nothing -> return ()

-- Prefer parameters which don't have an initial option, since those could
-- potentially become initial-only later on, and then we wouldn't need to
-- visit them at all
nextParameter :: MonadState (Set DAG) m
              => Set Variable
              -> m (Maybe ( (Variable, Set (Set Factor, Set Variable))
                          , Set Variable))
nextParameter vars = get <&> \dags -> do
  let fsSetV v = Set.map (varAssignment v) dags
      whenNoInitials v =
        let fsSet = fsSetV v
            hasInitials = any (Set.null . snd) fsSet
        in if hasInitials then Nothing else Just ((v, fsSet), Set.delete v vars)
  case msum (Set.map whenNoInitials vars) of
    Just res -> Just res
    Nothing ->
      Set.minView vars <&> \(v, without) -> ((v, fsSetV v), without)

varAssignment :: Variable -> DAG -> (Set Factor, Set Variable)
varAssignment v dag =
  (fromJust . Map.lookup v . dagVariables $ dag
  , setMapMaybe (\(par, chl) -> if chl == v then Just par else Nothing) . dagEdges $ dag
  )

queryFilterV :: (MonadState (Set DAG) m, MonadIO m)
             => (Variable, Set (Set Factor, Set Variable))
             -> m ()
queryFilterV (v, fsSet) = do
  dags <- get
  let noOptions = Set.null dags
  let onlyInitial = case Set.minView fsSet of
        Just ((facs, pars), rest) -> Set.null rest && Set.null pars
        _ -> False
  when (not (noOptions || onlyInitial)) $ do
    maybeFs <- query v fsSet
    let dags' = case maybeFs of
          Just fs -> Set.filter ((== Just fs) . Map.lookup v . dagVariables) dags
          Nothing -> Set.empty
    put dags'

query :: (MonadIO m)
      => Variable
      -> Set (Set Factor, Set Variable)
      -> m (Maybe (Set Factor))
query (Variable v) fs = liftIO $ do
  let fsMap = Map.fromList . zip [1..] . Set.toList $ fs
  putStrLn $ "\nWhich of the following sets of factors is a constant-normalized conditional density for the variable " ++ v ++ "?"
  putStrLn $ "  0: None of the below"
  forM_ (Map.toList fsMap) $ \(i, (fs, vs)) -> do
    let parNames = Set.toList $ Set.map (\(Variable v) -> v) vs
    let condStr =
          "lpdf(" ++ v ++ (if null parNames then "" else " | " ++ intercalate ", " parNames) ++ ") = "
    let showF (Factor f) = dropWhile (== '"') . dropWhileEnd (== '"') . show $ f
    let indentPluses = replicate 6 ' '
    let indentDelim = '\n' : indentPluses ++ "+ "
    let indentFirst = indentPluses ++ "  "
    putStrLn $ "  " ++ show i ++ ": " ++ condStr
    putStrLn $ indentFirst ++ intercalate indentDelim (map showF (Set.toList fs))

  let prompt = do
        putStr $ "Enter a number 0-" ++ show (Map.size fsMap) ++ ": "
        hFlush stdout
        nStr <- getLine
        case Read.readMaybe nStr of
          Just 0 -> return Nothing
          Just n -> case Map.lookup n fsMap of
            Just fs -> return (Just (fst fs))
            Nothing -> prompt
          Nothing -> prompt
  prompt
