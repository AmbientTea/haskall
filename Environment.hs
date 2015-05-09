module Environment where

import Data.Map (Map, insert, lookup, empty, toList)
import AbsHaskall
import Data.List (intercalate)

-- TYPES

data VType =
    IntType
    | BoolType
    | FuncType [VType] VType
    deriving (Eq, Ord, Show)
    
typeValue (IntVal _)  = IntType
typeValue (BoolVal _) = BoolType
typeValue (FunVal names types env exp tp) = FuncType types tp

typeToken TInt = IntType
typeToken TBool = BoolType
typeToken (TFunc types tp) = FuncType (map typeToken types) (typeToken tp)

-- VALUES

data Value =
    IntVal Integer
    | BoolVal Bool
    | FunVal [String] [VType] Env Exp VType
    deriving (Eq, Ord, Show)

int  (IntVal i)  = i
bool (BoolVal b) = b

liftValOp f unp1 unp2 pck v1 v2 = pck $ f (unp1 v1) (unp2 v2)

valAdd = liftValOp (+) int int IntVal
valMul = liftValOp (*) int int IntVal
valSub = liftValOp (-) int int IntVal

valLt = liftValOp (<) int int BoolVal

valIntEq = liftValOp (==) int int BoolVal
valBoolEq = liftValOp (==) bool bool BoolVal


-- ENVIRONMENT

data Env = Env {
    keys :: Map String (Integer, VType)
    } deriving (Eq, Ord)

instance Show Env where
    show env = let
        inShow (name, (pos, tp)) = name ++ " : " ++ (show tp) ++ " -> " ++ (show pos)
        in intercalate "\n" $ map inShow $ toList $ keys env

data State = State {
    nextKey :: Integer,
    store :: Map Integer Value
    } deriving (Eq, Ord, Show)
    
emptyEnv = Env empty
emptyState = State 0 empty

insertStore k v s = State (nextKey s) (insert k v (store s))
lookupStore k s = Data.Map.lookup k (store s)

getVarType var env = case Data.Map.lookup var (keys env) of
    Nothing -> Left $ "cannot type: variable " ++ (show var) ++ " not found in env " ++ (show env)
    Just (_, t) -> Right t

getVar :: String -> Env -> State -> Either String Value
getVar var env state = case Data.Map.lookup var (keys env) of
    Nothing -> Left $ "cannot get: variable " ++ (show var) ++ " not found in env " ++ (show env)
    Just (p, _) -> case lookupStore p state of
        Nothing -> Left $ "uninitialized variable " ++ (show var)
        Just v  -> Right v

setVar :: String -> Env -> Value -> State -> Either String State
setVar var env val state = case Data.Map.lookup var (keys env) of
    Nothing -> Left $ "cannot set: variable " ++ (show var) ++ " not found in env " ++ (show env)
    Just (p, t) -> let t2 = typeValue val in if t2 == t
        then Right $ insertStore p val state
        else Left $ "cannot assign value " ++ (show val) ++ " of type " ++
            (show t2) ++ " to variable " ++ (show var) ++ " of type " ++
            (show t)

createVar var t en st = let
        newKey = nextKey st
    in (Env (insert var (newKey, t) (keys en)), State (newKey+1) (store st))

createVars :: ([String], [VType]) -> Env -> State -> (Env,State)
createVars ([],[]) en st = (en, st)
createVars (n:nt, t:tt) en st = let
        (ne, ns) = createVar n t en st
    in createVars (nt,tt) ne ns

setVars :: [ (String, Value) ] -> Env -> State -> Either String State
setVars [] en st = Right st
setVars ((var, val) : tl) en st = case setVar var en val st of
    Left err -> Left err
    Right nst -> setVars tl en nst
