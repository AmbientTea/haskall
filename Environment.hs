module Environment where
import Values
import Types

import Data.Map (Map, insert, lookup, empty)

data Env = Env {
    nextKey :: Integer,
    keys :: Map String (Integer, VType)
    } deriving (Eq, Ord, Show)

type State = Map Integer Value

emptyEnv = Env 0 empty
emptyState = empty

getVarType var env = case Data.Map.lookup var (keys env) of
    Nothing -> Left $ "variable " ++ (show var) ++ " not declared"
    Just (_, t) -> Right t

getVar :: String -> Env -> State -> Either String Value
getVar var env state = case Data.Map.lookup var (keys env) of
    Nothing -> Left $ "variable " ++ (show var) ++ " not found"
    Just (p, _) -> case Data.Map.lookup p state of
        Nothing -> Left $ "uninitialized variable " ++ (show var)
        Just v  -> Right v

setVar :: String -> Env -> Value -> State -> Either String State
setVar var env val state = case Data.Map.lookup var (keys env) of
    Nothing -> Left $ "variable " ++ (show var) ++ " not found"
    Just (p, t) -> let t2 = typeValue val in if t2 == t
        then Right $ insert p val state
        else Left $ "cannot assign value " ++ (show val) ++ " of type " ++
            (show t2) ++ " to variable " ++ (show var) ++ " of type " ++ (show t)

createVar var t en = let
        newKey = nextKey en
    in Env (newKey + 1) (insert var (newKey, t) (keys en))
