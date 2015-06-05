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
    | StringType
    | FuncType [VType] VType
    deriving (Eq, Ord)

inbuiltTypes = fromList [
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
    
typeValue (IntVal _)  = IntType
typeValue (BoolVal _) = BoolType
typeValue (StringVal _) = StringType
typeValue (FunVal names types env st exp tp) = FuncType types tp

typeToToken :: VType -> Type
typeToToken IntType = TType (Ident "int")
typeToToken BoolType = TType (Ident "bool")
typeToToken StringType = TType (Ident "string")
typeToToken (FuncType args tp) = TFunc (map typeToToken args) (typeToToken tp)

-- VALUES

data Value =
    IntVal Integer
    | BoolVal Bool
    | StringVal String
    | FunVal [String] [VType] Env State Exp VType

instance Show Value where
    show (IntVal i) = show i
    show (BoolVal b) = show b
    show (StringVal str) = str
    show (FunVal args types env st exp tp) =
        "fun (" ++ (intercalate ", " args) ++ ") = " ++ (printTree exp)

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

data Procedure = Proc {
        pArgTypes :: [VType],
        pArgNames :: [String],
        pCont :: State -> Either Exception State,
        pRet :: State -> TryValue,
        pEnv :: Env
    }
instance Show Procedure where
    show p = "proc " ++ (show $ pArgTypes p)

data Env = Env {
    nextKey :: Integer,
    keys :: Map String EnvElem,
    types :: Map String VType,
    procs :: Map String Procedure
    }

instance Show Env where
    show env = let
            inShow (name, (pos, tp)) = name ++ " : " ++ (show tp)
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
    store :: Map Integer Value,
    output :: String
    }
    | StackedState {
        topState :: State,
        restState :: State
    } deriving Show

emptyState = State empty ""

lookupStore loc (State stor _) = Data.Map.lookup loc stor
lookupStore loc (StackedState top bot) = case lookupStore loc top of
    Just v -> Just v
    Nothing -> lookupStore loc bot

getFromStore loc st = fromJust $ lookupStore loc st

setInStore val loc (State stor out) = State (insert loc val stor) out
setInStore val loc (StackedState top bot) =
    StackedState (setInStore val loc top) bot

pushToOut (State stor out) str = State stor (out ++ str)
pushToOut (StackedState top bot) str =
    StackedState top (pushToOut bot str)

------------------------

lookupVarValue var env st = fmap (flip lookupStore $ st) (lookupLoc var env)

createEmptyVar :: String -> VType -> Env -> Env
createEmptyVar var tp env = let
        (loc, newEnv) = addToEnv var tp env
    in newEnv

getVarValue var env st = getFromStore (getLoc var env) st
setVarValue var env val st = setInStore val (getLoc var env) st

setValues :: [(String,Value)] -> Env -> State -> State
setValues [] env st = st
setValues ((var, val):rest) env st =
    setValues rest env (setVarValue var env val st)

createVar var tp env val st = let
        (loc, newEnv) = addToEnv var tp env
        newSt = setInStore val loc st
    in (newEnv, newSt)


