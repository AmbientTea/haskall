module Environment where

import Data.Map (Map, insert, lookup, empty, toList)
import AbsHaskall
import PrintHaskall
import Data.List (intercalate)

-- Error Handling

data Exception =
    Exception String
    | NestedException Exception String
    | TypingException VType VType Exp
    | ConditionException Exp VType
    | UntypedArgumentException Exp
    | BadArgumentsException [Exp] [VType] String VType 
    | ZeroDivisionException
    | NotDeclaredException String Env
    | UninitializedException String
    | AssignmentTypeException String VType Value VType
    -- | NotDeclaredException

instance Show Exception where
    show (Exception mess) = "exception : " ++ mess
    show (NestedException ex mess) = mess ++ ", caused by: " ++ (show ex)
    show (TypingException expT realT expr) =
        "typing error: expected type " ++ (show expT) ++ " but expression " ++
        (printTree expr) ++ " has type " ++ (show realT)
    show (ConditionException exp tp) = 
        "typing error: expression " ++ (printTree exp) ++ " of type " ++
        (show tp) ++ " as condition in if/loop"
    show (UntypedArgumentException exp) =
        "untyped arguments in function " ++ (printTree exp) ++
        " are now allowed"
    show (BadArgumentsException args types fun tp) =
        "cannot apply arguments " ++ (intercalate ", " $ map printTree args)
        ++ " of types " ++ (intercalate ", " $ map show types) ++
        " to function " ++ fun ++ " of type " ++ (show tp)
    show (ZeroDivisionException) = "division by 0"
    show (NotDeclaredException var env) = "variable " ++ var ++
        " not declared in env: \n" ++ (show env)
    show (UninitializedException var) = "variable " ++ var ++ " accessed but "
        ++ "not initialized"
    show (AssignmentTypeException var vtp val vatp) = "cannot assign value "
        ++ (show val) ++ " of type " ++ (show vatp) ++ " to variable " ++ var
        ++ " of type " ++ (show vtp)

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
typeValue (FunVal names types env exp tp) = FuncType types tp

typeToken TInt = IntType
typeToken TBool = BoolType
typeToken (TFunc types tp) = FuncType (map typeToken types) (typeToken tp)

-- VALUES

data Value =
    IntVal Integer
    | BoolVal Bool
    | FunVal [String] [VType] Env Exp VType
    deriving (Eq, Ord)

instance Show Value where
    show (IntVal i) = show i
    show (BoolVal b) = show b
    show (FunVal args types env exp tp) =
        "fun (" ++ (intercalate ", " args) ++ ") = " ++ (printTree exp)

int  (IntVal i)  = i
bool (BoolVal b) = b

liftValOp f unp1 unp2 pck v1 v2 = pck $ f (unp1 v1) (unp2 v2)

valAdd = liftValOp (+) int int IntVal
valMul = liftValOp (*) int int IntVal
valSub = liftValOp (-) int int IntVal
valDiv = liftValOp (div) int int IntVal

valLt = liftValOp (<) int int BoolVal

valIntEq = liftValOp (==) int int BoolVal
valBoolEq = liftValOp (==) bool bool BoolVal


-- ENVIRONMENT

data Env = Env {
    keys :: Map String (Integer, VType)
    } deriving (Eq, Ord)

instance Show Env where
    show env = let
        inShow (name, (pos, tp)) = name ++ " : " ++ (show tp)
        in intercalate "\n" $ map inShow $ toList $ keys env

data State = State {
    nextKey :: Integer,
    store :: Map Integer Value
    } deriving (Eq, Ord)

instance Show State where
    show s = "state: \n" ++ (intercalate "\n" $ map
        (\(k,v) -> (show k) ++ " : " ++ (show v))
        $ toList $ store s)

emptyEnv = Env empty
emptyState = State 0 empty

insertStore k v s = State (nextKey s) (insert k v (store s))
lookupStore k s = Data.Map.lookup k (store s)

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
