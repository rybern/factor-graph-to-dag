module Query where

import System.IO
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Control.Monad.State
import Data.Maybe
import qualified Text.Read as Read

import Types

queryFilterAll :: Set Variable -> Set DAG -> IO (Maybe DAG)
queryFilterAll ignore dags = case Set.lookupMin dags of
  Nothing -> return Nothing
  Just dag -> (Set.lookupMin <$>) . flip execStateT dags $
              forM_ (filter (`Set.notMember` ignore) . Map.keys . dagVariables $ dag)
                      queryFilterV

queryFilterV :: Variable -> StateT (Set DAG) IO ()
queryFilterV v = do
  dags <- get
  when (not (Set.null dags)) $ do
    let fsSet = Set.map (fromJust . Map.lookup v . dagVariables) dags
    maybeFs <- lift $ query v fsSet
    let dags' = case maybeFs of
          Just fs -> Set.filter ((== Just fs) . Map.lookup v . dagVariables) dags
          Nothing -> Set.empty
    put dags'

query :: Variable -> Set (Set Factor) -> IO (Maybe (Set Factor))
query (Variable v) fs = do
  let fsMap = Map.fromList . zip [1..] . Set.toList $ fs
  putStrLn ""
  putStrLn $ "Which of the following sets of factors is a constant-normalized conditional density for the variable " ++ v ++ "?"
  putStrLn $ "  0: None of the below"
  forM_ (Map.toList fsMap) $ \(i, fs) -> do
    putStrLn $ "  " ++ show i ++ ":"
    forM_ fs $ (\(Factor f) ->
      putStrLn $ "    " ++ show f)

  let prompt = do
        putStr $ "Enter a number 0-" ++ show (Map.size fsMap) ++ ": "
        hFlush stdout
        nStr <- getLine
        case Read.readMaybe nStr of
          Just 0 -> return Nothing
          Just n -> case Map.lookup n fsMap of
            Just fs -> return (Just fs)
            Nothing -> prompt
          Nothing -> prompt
  prompt
