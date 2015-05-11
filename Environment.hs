module Environment where

import Data.Map (Map, insert, lookup, empty, toList)
import AbsHaskall
import PrintHaskall
import Data.List (intercalate)
import Data.Maybe

-- Error Handling

data Exception =
    Exception String
    | NestedException Exception String
    | ZeroDivisionException
    | UninitializedException String

instance Show Exception where
    show (Exception mess) = "exception : " ++ mess
    show (NestedException ex mess) = mess ++ ", caused by: " ++ (show ex)
    show (ZeroDivisionException) = "division by 0"
    show (UninitializedException var) = "variable " ++ var ++ " accessed but "
        ++ "not initialized"

throw str = Left $ Exception str

-- TYPES

data VType =
    IntType
    | BoolType
    | FuncType [VType] VType
    deriving (Eq, Ord)

instance Show VType where
    show IntType = "int"
    show BoolType = "bool"
    show (FuncType args tp) =
        "(" ++ (intercalate ", " $ map show args) ++ ") => " ++ (show tp)
    
typeValue (IntVal _)  = IntType
typeValue (BoolVal _) = BoolType
typeValue (FunVal names types env st exp tp) = FuncType types tp

typeToken TInt = IntType
typeToken TBool = BoolType
typeToken (TFunc types tp) = FuncType (map typeToken types) (typeToken tp)

-- VALUES

data Value =
    IntVal Integer
    | BoolVal Bool
    | FunVal [String] [VType] Env State Exp VType
    deriving (Eq, Ord)

instance Show Value where
    show (IntVal i) = show i
    show (BoolVal b) = show b
    show (FunVal args types env st exp tp) =
        "fun (" ++ (intercalate ", " args) ++ ") = " ++ (printTree exp)

type TryValue = Either Exception Value
type Operator = Value -> Value -> TryValue

unright (Right r) = r

int  (IntVal i)  = i
bool (BoolVal b) = b

liftValOp :: (a->b->c) -> (Value->a) -> (Value->b) -> (c->Value) -> Value -> Value -> Value
liftValOp f unp1 unp2 pck v1 v2 = pck $ f (unp1 v1) (unp2 v2)

valAdd v1 v2 = Right (liftValOp (+) int int IntVal v1 v2)
valMul v1 v2 = Right (liftValOp (*) int int IntVal v1 v2)
valSub v1 v2 = Right (liftValOp (-) int int IntVal v1 v2)
valDiv v1 v2 = case v2 of
    IntVal 0 -> Left ZeroDivisionException
    _ -> Right $ liftValOp (div) int int IntVal v1 v2


valEq v1 v2 = case (v1,v2) of
    (IntVal i1, IntVal i2) -> Right $ BoolVal $ i1 == i2
    (BoolVal b1, BoolVal b2) -> Right $ BoolVal $ b1 == b2

valLt v1 v2 = Right $ liftValOp (<) int int BoolVal v1 v2

-- ENVIRONMENT

type EnvElem = (Integer, VType)



data Env = Env {
    keys :: Map String EnvElem
    } deriving (Eq, Ord)

instance Show Env where
    show env = let
        inShow (name, (pos, tp)) = name ++ " : " ++ (show tp)
        in intercalate "\n" $ map inShow $ toList $ keys env

emptyEnv = Env empty

lookupEnv var env = Data.Map.lookup var (keys env)
getFromEnv var env = fromJust $ lookupEnv var env

lookupLoc var env = fmap fst (lookupEnv var env)
lookupType var env = fmap snd (lookupEnv var env)

getLoc var env = fromJust $ lookupLoc var env
getType var env = fromJust $ lookupType var env

addToEnv var loc tp env = Env (insert var (loc,tp) (keys env))

-- STATE

data State = State {
    nextKey :: Integer,
    store :: Map Integer Value
    } deriving (Eq, Ord)

instance Show State where
    show s = "state: \n" ++ (intercalate "\n" $ map
        (\(k,v) -> (show k) ++ " : " ++ (show v))
        $ toList $ store s)

emptyState = State 0 empty

lookupStore loc st = Data.Map.lookup loc (store st)
getFromStore loc st = fromJust $ lookupStore loc st

addToStore :: Value -> State -> (Integer, State)
addToStore val st = let
        loc = nextKey st
    in (loc, State (loc+1) (insert loc val (store st)))

addEmptyToStore st = let loc = nextKey st in (loc, State (loc+1) (store st))

setInStore val loc st = State (nextKey st) (insert loc val (store st))

------------------------

lookupVarValue var env st = fmap (flip lookupStore $ st) (lookupLoc var env)

createVar var tp env val st = let
        (loc, newSt) = addToStore val st
        newEnv = addToEnv var loc tp env
    in (newEnv, newSt)

createEmptyVar var tp env st = let
        (loc, newSt) = addEmptyToStore st
        newEnv = addToEnv var loc tp env
    in (newEnv, newSt)

getVarValue var env st = getFromStore (getLoc var env) st
setVarValue var env val st = setInStore val (getLoc var env) st

setValues [] env st = st
setValues ((var, val):rest) env st =
    setValues rest env (setVarValue var env val st)

{-
insertStore k v s = State (nextKey s) (insert k v (store s))
lookupStore k s = Data.Map.lookup k (store s)

insertLoc var env loc tp = Env (insert var (loc,tp) (keys env))
lookupLoc var env = fst . fromJust $ Data.Map.lookup var (keys env)

getVarValue :: String -> Env -> State -> Value
getVarValue var env st = fromJust $ lookupStore (lookupLoc var env) st

addNewVar :: String -> Env -> VType -> Value -> State -> (Env,State)
addNewVar var env tp val st = let
        loc = nextKey st
        newEnv = insertLoc var env loc tp
        newSt = State (loc+1) (insert var val $ store st)
    in (newEnv, newSt)

getVarType var env = case Data.Map.lookup var (keys env) of
    Nothing -> Left $ NotDeclaredException var env
    Just (_, t) -> Right t

getVar :: String -> Env -> State -> Either Exception Value
getVar var env state = case Data.Map.lookup var (keys env) of
    Nothing -> Left $ NotDeclaredException var env
    Just (p, _) -> case lookupStore p state of
        Nothing -> Left $ UninitializedException var
        Just v  -> Right v

setVar :: String -> Env -> Value -> State -> Either Exception State
setVar var env val state = case Data.Map.lookup var (keys env) of
    Nothing -> Left $ NotDeclaredException var env
    Just (p, t) -> let t2 = typeValue val in if t2 == t
        then Right $ insertStore p val state
        else Left $ AssignmentTypeException var t val t2

createVar var t en st = let
        newKey = nextKey st
    in (Env (insert var (newKey, t) (keys en)), State (newKey+1) (store st))

createVars :: ([String], [VType]) -> Env -> State -> (Env,State)
createVars ([],[]) en st = (en, st)
createVars (n:nt, t:tt) en st = let
        (ne, ns) = createVar n t en st
    in createVars (nt,tt) ne ns

setVars :: [ (String, Value) ] -> Env -> State -> Either Exception State
setVars [] en st = Right st
setVars ((var, val) : tl) en st = case setVar var en val st of
    Left err -> Left err
    Right nst -> setVars tl en nst
    
    -}
