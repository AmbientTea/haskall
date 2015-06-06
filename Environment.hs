module Environment where

import Data.Map (Map, insert, lookup, empty, toList, fromList)
import AbsHaskall
import PrintHaskall
import Data.List (intercalate)
import Data.Maybe

-- Error Handling

data Exception =
    Exception String
    | NestedException Exception String
    | ZeroDivisionException
    | UninitializedException String Env State

instance Show Exception where
    show (Exception mess) = "exception : " ++ mess
    show (NestedException ex mess) = mess ++ ", caused by: " ++ (show ex)
    show (ZeroDivisionException) = "division by 0"
    show (UninitializedException var env st) = "variable " ++ var ++
        " accessed but " ++ "not initialized in env:\n" ++ (show env) ++ "\n"
        ++ (show st)

throw str = Left $ Exception str

-- TYPES
data Constr = Constr String [VType] deriving (Eq, Ord)

data VType =
    UnitType
    | IntType
    | BoolType
    | StringType
    | FuncType [VType] VType
    | AlgType String [Constr]
    deriving (Eq, Ord)

inbuiltTypes = fromList [
        ("unit", UnitType),
        ("int", IntType),
        ("bool", BoolType),
        ("string", StringType)
    ]

instance Show VType where
    show IntType = "int"
    show BoolType = "bool"
    show (FuncType args tp) =
        "(" ++ (intercalate ", " $ map show args) ++ ") => " ++ (show tp)
    show StringType = "string"
    show UnitType = "unit"
    show (AlgType name _) = name

typeToToken :: VType -> Type
typeToToken UnitType = TType (Ident "unit")
typeToToken IntType = TType (Ident "int")
typeToToken BoolType = TType (Ident "bool")
typeToToken StringType = TType (Ident "string")
typeToToken (FuncType args tp) = TFunc (map typeToToken args) (typeToToken tp)
typeToToken (AlgType name _) = TType (Ident name)

--FunVal [String] [VType] Env State Exp VType
constrToFun tp (Constr name types) = FunVal types cont tp where
    cont args = Right $  AlgVal (Constr name types) args

-- VALUES

data Value =
    UnitVal
    | IntVal Integer
    | BoolVal Bool
    | StringVal String
    | FunVal [VType] ([Value] -> TryValue) VType
    | AlgVal Constr [Value]

instance Show Value where
    show UnitVal = "unit"
    show (IntVal i) = show i
    show (BoolVal b) = show b
    show (StringVal str) = str
    show (FunVal types cont tp) =
        "function"
    show (AlgVal (Constr name _) values) = name ++ (show values)

type TryValue = Either Exception Value
type Operator = Value -> Value -> TryValue

unright (Right r) = r

int  (IntVal i)  = i
bool (BoolVal b) = b

liftValOp :: (a->b->c) -> (Value->a) -> (Value->b) -> (c->Value) -> Value -> Value -> Value
liftValOp f unp1 unp2 pck v1 v2 = pck $ f (unp1 v1) (unp2 v2)

valMul v1 v2 = Right (liftValOp (*) int int IntVal v1 v2)
valSub v1 v2 = Right (liftValOp (-) int int IntVal v1 v2)
valDiv v1 v2 = case v2 of
    IntVal 0 -> Left ZeroDivisionException
    _ -> Right $ liftValOp (div) int int IntVal v1 v2

valAdd v1 v2 = case (v1,v2) of
    (IntVal i1, IntVal i2) -> Right $ IntVal $ i1 + i2
    (StringVal s1, StringVal s2) -> Right $ StringVal $ s1 ++ s2

valEq v1 v2 = case (v1,v2) of
    (IntVal i1, IntVal i2) -> Right $ BoolVal $ i1 == i2
    (BoolVal b1, BoolVal b2) -> Right $ BoolVal $ b1 == b2
    (StringVal s1, StringVal s2) -> Right $ BoolVal $ s1 == s2

valLt v1 v2 = Right $ liftValOp (<) int int BoolVal v1 v2

-- ENVIRONMENT

type EnvElem = (Integer, VType)

type Prog = State -> IO (Either Exception State)

data Procedure = Proc {
        pArgTypes :: [VType],
        pArgNames :: [String],
        pCont :: Prog,
        pRet :: State -> TryValue,
        pEnv :: Env,
        pRetType :: VType
    }
instance Show Procedure where
    show p = "proc " ++ (show $ pArgTypes p) ++ " {" ++ (show $ pEnv p) ++ "}\n"

data Env = Env {
    nextKey :: Integer,
    keys :: Map String EnvElem,
    types :: Map String VType,
    procs :: Map String Procedure
    }

instance Show Env where
    show env = let
            inShow (name, (pos, tp)) = "[" ++ (show pos) ++ "]" ++ name ++ " : " ++ (show tp)
            varL = intercalate "\n" $ map inShow $ toList $ keys env
            procsShow (name, proc) = name ++ " : " ++ (show proc)
            procL = intercalate "\n" $ map procsShow $ toList $ procs env
        in "variables:\n" ++ varL ++ "\nprocedures:\n" ++ procL

emptyEnv = Env 0 empty inbuiltTypes empty

lookupEnv var env = Data.Map.lookup var (keys env)
getFromEnv var env = fromJust $ lookupEnv var env

lookupLoc var env = fmap fst (lookupEnv var env)
lookupType var env = fmap snd (lookupEnv var env)

getLoc var env = fromJust $ lookupLoc var env
getType var env = fromJust $ lookupType var env

addToEnv var tp env = (nextKey env,
                     Env ((nextKey env) + 1)
                          (insert var (nextKey env,tp) (keys env))
                          (types env) (procs env))

addType name tp env = Env (nextKey env) (keys env) (insert name tp (types env) ) (procs env)

addProc name proc env = Env (nextKey env) (keys env) (types env) (insert name proc $ procs env)
lookupProc name env = Data.Map.lookup name (procs env)

-- STATE

data State = State {
    store :: Map Integer Value
    }
    | StackedState {
        topState :: State,
        restState :: State
    }
instance Show State where
    show (StackedState top bot) = (show top) ++ "\n----\n" ++ (show bot)
    show (State stor) = let
            showPair (loc, val) = (show loc) ++ ": " ++ (show val)
            lines = intercalate "\n" $ map showPair $ toList stor
        in "store:\n" ++ lines

emptyState = State empty

lookupStore loc (State stor) = Data.Map.lookup loc stor
lookupStore loc (StackedState top bot) = case lookupStore loc top of
    Just v -> Just v
    Nothing -> lookupStore loc bot

getFromStore loc st = fromJust $ lookupStore loc st

setInStore val loc (State stor) = State (insert loc val stor)
setInStore val loc (StackedState top bot) =
    case lookupStore loc top of
        Just _ -> StackedState (setInStore val loc top) bot
        Nothing -> StackedState top (setInStore val loc bot)

addToStore val loc (State stor) = State (insert loc val stor)
addToStore val loc (StackedState top bot) = StackedState (addToStore val loc top) bot

------------------------

lookupVarValue :: String -> Env -> State -> Maybe Value
lookupVarValue var env st = (lookupLoc var env) >>= (flip lookupStore $ st)
-- lookupVarValue var env st = lookupStore (getLoc var env) st

createEmptyVar :: String -> VType -> Env -> Env
createEmptyVar var tp env = let
        (loc, newEnv) = addToEnv var tp env
    in newEnv

createEmptyVars [] env = env
createEmptyVars ((var,tp):rest) env =
    createEmptyVars rest (createEmptyVar var tp env)

setVarValue var env val st = setInStore val (getLoc var env) st

setValues :: [(String,Value)] -> Env -> State -> State
setValues [] env st = st
setValues ((var, val):rest) env st =
    setValues rest env (setVarValue var env val st)

createVar var tp env val st = let
        (loc, newEnv) = addToEnv var tp env
        newSt = setInStore val loc st
    in (newEnv, newSt)


