module Expressions where
import AbsHaskall
import Environment
import PrintHaskall

import Data.Either
import Data.List

compileExpression :: Exp -> Env -> Either TypingError (State -> TryValue)
compileExpression exp env = case typeExp exp env of
        -- Right (expType, typedExp) -> Left $ TypingError $ (show expType) ++ " \n " ++ (printTree typedExp) ++ "\n" ++ (show typedExp)
        Right (expType, typedExp) -> Right $ compExp env typedExp
        Left err -> Left err

-- DECLARATIONS

-- function arguments
addArgument :: ArgDec -> Env -> Env
addArgument (TArgDec (Ident arg) tp) env = createEmptyVar arg (typeToken tp) env

addArguments :: [ArgDec] -> Env -> Env
addArguments [] env = env
addArguments (arg:rest) env = let
        newEnv= addArgument arg env
    in addArguments rest newEnv

argTypes args = map (\(TArgDec _ tp) -> typeToken tp) args
argNames args = map (\(TArgDec (Ident arg) _) -> arg) args



-- TYPING

data TypingError = 
    UnexpectedTypeError VType VType Exp
    | ConditionTypingError Exp VType
    | UntypedArgumentError Exp
    | ArgumentTypingError [Exp] [VType] Exp VType
    | AssignmentTypingError String VType Exp VType
    | NotDeclaredError String Env
    
    | IfTypingError Exp VType VType
    | EqTypingError Exp VType VType
    | NotAFunctionError Exp VType
    | FunctionTypeError Exp VType VType
    | TypingError String

untype str = Left $ TypingError str

instance Show TypingError where
    show (UnexpectedTypeError expT realT expr) =
        "typing error: expected type " ++ (show expT) ++ " but expression " ++
        (printTree expr) ++ " has type " ++ (show realT)
    show (ConditionTypingError exp tp) = 
        "typing error: expression " ++ (printTree exp) ++ " of type " ++
        (show tp) ++ " as condition in if/loop"
    show (UntypedArgumentError exp) =
        "typing error: untyped arguments in function " ++ (printTree exp) ++
        " are now allowed"
    show (ArgumentTypingError args types fun tp) =
        "cannot apply arguments " ++ (intercalate ", " $ map printTree args)
        ++ " of types " ++ (intercalate ", " $ map show types) ++
        " to function " ++ (printTree fun) ++ " of type " ++ (show tp)
    show (AssignmentTypingError var vtp val vatp) = "cannot assign value "
        ++ (show val) ++ " of type " ++ (show vatp) ++ " to variable " ++ var
        ++ " of type " ++ (show vtp)
    show (NotDeclaredError var env) = "variable " ++ var ++
        " not declared in env: \n" ++ (show env)
    show (IfTypingError exp tp1 tp2) = "typing error: two branches of an if "
        ++ "statement " ++ (printTree exp) ++ " have different types " ++
        (show tp1) ++ " and " ++ (show tp2)
    show (EqTypingError exp tp1 tp2) = "typing error: cannot compare values "
        ++ "of types " ++ (show tp1) ++ " and " ++ (show tp2) ++ " in " ++
        (printTree exp)
    show (NotAFunctionError exp tp) = "typing error: expression " ++
        (printTree exp) ++ " of type " ++ (show tp) ++ " is not a function"
    show (FunctionTypeError exp tp1 tp2) = "typing error: function " ++
        (printTree exp) ++ " declares type " ++ (show tp1) ++ " but has type "
        ++ (show tp2)
    show (TypingError str) = "typing error: " ++ str

expectType tp exp env = case typeExp exp env of
    Left err -> Left err
    Right (expType, typedExp) -> if tp == expType
        then Right $ (expType, typedExp)
        else Left $ UnexpectedTypeError tp expType exp

typeBoth e1 e2 t1 t2 tf c env = case expectType t1 e1 env of
    Left err -> Left err
    Right (_, exp1) -> case expectType t2 e2 env of
        Left err -> Left err
        Right (_, exp2) -> Right (tf, c exp1 exp2)

typeExpList :: [Exp] -> Env -> Either TypingError [(VType, Exp)]
typeExpList exps env = let types = map (flip typeExp env) exps in
    case lefts types of
        [] -> Right $ rights types
        lst -> Left $ head lst

-- check whether expression types properly in env and returns the type and
-- full-typed version of this expression
typeExp :: Exp -> Env -> Either TypingError (VType,Exp)

typeExp (EIf cond e1 e2) env = case typeExp cond env of
    Left err -> Left err
    Right (condType, typedCond) -> if condType /= BoolType
        then Left $ ConditionTypingError (EIf cond e1 e2) condType
        else case (typeExp e1 env, typeExp e2 env) of
            (Left err, _) -> Left err
            (_, Left err) -> Left err
            (Right (type1, exp1), Right (type2, exp2)) -> if type1 == type2
                then Right (type1, EIf typedCond exp1 exp2)
                else Left $ IfTypingError (EIf cond e1 e2) type1 type2


typeExp (ELt e1 e2) env = typeBoth e1 e2 IntType IntType BoolType ELt env
typeExp (EEq e1 e2) env = case (typeExp e1 env, typeExp e2 env) of
    (Right (type1, exp1), Right (type2, exp2)) -> case (type1,type2) of
        (IntType,IntType)   -> Right (BoolType, EEq exp1 exp2)
        (BoolType,BoolType) -> Right (BoolType, EEq exp1 exp2)
        (StringType,StringType) -> Right (StringType, EEq exp1 exp2)
        _ -> Left $ EqTypingError (EEq e1 e2) type1 type2
    (Left err, _) -> Left err
    (_, Left err) -> Left err

typeExp (EFunc args tp exp) env = let
        funEnv = addArguments args env
        eType = typeToken tp
    in case typeExp exp funEnv of
        Left err -> Left err
        Right (funType, typedExp) -> if funType == eType
            then Right (FuncType (argTypes args) eType, EFunc args tp typedExp)
            else Left $ FunctionTypeError (EFunc args tp exp) eType funType

typeExp (ENFunc (Ident fun) args tp exp) env = let
        atypes = argTypes args
        (_, funEnv) = addToEnv fun (FuncType atypes (typeToken tp)) env
    in case typeExp (EFunc args tp exp) funEnv of
        Left err -> Left err
        Right (funType, (EFunc args tp exp)) ->
            Right (funType, ENFunc (Ident fun) args tp exp)

typeExp (Call funExp args) env = case typeExp funExp env of
    Left err -> Left err
    Right (FuncType types retTp, typedFunExp) -> case typeExpList args env of
        Left err -> Left err
        Right argTpList -> let (argTypes, typedArgs) = unzip argTpList in
            if argTypes == types
                then Right $ (retTp, Call typedFunExp typedArgs)
                else Left $ ArgumentTypingError args argTypes funExp (FuncType types retTp)
    Right (tp, exp) -> Left $ NotAFunctionError exp tp


typeExp (ELet [] exp) env = case typeExp exp env of
    Left err -> Left err
    Right (expTp, tpExp) -> Right $ (expTp, ELet [] tpExp)

typeExp (ELet (dh:decls) exp) env = let
        typeDecl (FSUnTDec var varExp) =
            case typeExp varExp env of
                Left err -> Left err
                Right (expTp, tpExp) ->
                        Right $ FSTDec var (typeToToken expTp) tpExp
        typeDecl (FSTDec var varTp varExp) =
            case expectType (typeToken varTp) varExp env of
                Left err -> Left err
                Right (expTp, tpExp) ->
                        Right $ FSTDec var (typeToToken expTp) tpExp
    in case typeDecl dh of
        Left err -> Left err
        Right tpDecl -> let
                (FSTDec (Ident var) varTP varExp) = tpDecl
                (loc, letEnv) = addToEnv var (typeToken varTP) env
            in case typeExp (ELet decls exp) letEnv of
                Left err -> Left err
                Right (letTp, ELet fdecls fexp) ->
                    Right $ (letTp, ELet (tpDecl:fdecls) fexp)


typeExp (EAdd e1 e2) env = typeBoth e1 e2 IntType IntType IntType EAdd env
typeExp (ESub e1 e2) env = typeBoth e1 e2 IntType IntType IntType ESub env
typeExp (EMul e1 e2) env = typeBoth e1 e2 IntType IntType IntType EMul env
typeExp (EDiv e1 e2) env = typeBoth e1 e2 IntType IntType IntType EDiv env

typeExp e env = Right $ case e of
    ETrue  -> (BoolType, e)
    EFalse -> (BoolType, e)
    EInt i -> (IntType, e)
    EVar (Ident var) -> (getType var env, e)
    EString str -> (StringType, EString str)
    


-- SEMANTICS

eitherPair f e1 e2 = case (e1,e2) of (Right v1, Right v2) -> f v1 v2

intOp env op e1 e2 st =
    Right $ eitherPair op (compExp env e1 st) (compExp env e2 st)

unpackApply :: Operator -> TryValue -> TryValue -> TryValue
unpackApply op v1 v2 = case (v1,v2) of
    (Right v1, Right v2) -> op v1 v2
    (Left err, _) -> Left err
    (_, Left err) -> Left err

opComp :: Env -> Operator -> Exp -> Exp -> State -> TryValue
opComp env op e1 e2 st =
    unpackApply op (compExp env e1 st) (compExp env e2 st)

compExp :: Env -> Exp -> State -> TryValue
compExp env (ETrue ) st = Right $ BoolVal True
compExp env (EFalse) st = Right $ BoolVal False
compExp env (EInt i) st = Right $ IntVal i
compExp env (EString str) st = Right $ StringVal str

compExp env (EAdd e1 e2) st = opComp env valAdd e1 e2 st
compExp env (ESub e1 e2) st = opComp env valSub e1 e2 st
compExp env (EMul e1 e2) st = opComp env valMul e1 e2 st
compExp env (EDiv e1 e2) st = opComp env valDiv e1 e2 st

compExp env (EEq e1 e2) st = opComp env valEq e1 e2 st
compExp env (ELt e1 e2) st = opComp env valLt e1 e2 st

compExp env (EIf e1 e2 e3) st = case compExp env e1 st of
    Right (BoolVal True)  -> compExp env e2 st
    Right (BoolVal False) -> compExp env e3 st

compExp env (EVar (Ident var)) st = Right $ getVarValue var env st

compExp env (ELet [] exp) st = compExp env exp st
compExp env (ELet ((FSTDec (Ident var) tp vexp):rest) exp) st =
    case compExp env vexp st of
        Left err -> Left err
        Right val -> let
                (newEnv, newSt) = createVar var (typeToken tp) env val st
            in compExp newEnv (ELet rest exp) newSt

compExp env (ELet ((FSUnTDec (Ident var) vexp):rest) exp) st = undefined

compExp env (EFunc decls tp exp) st = let
        funEnv = addArguments decls env
    in Right $ FunVal (argNames decls) (argTypes decls) funEnv
                                                    st exp (typeToken tp)

compExp env (ENFunc (Ident fun) decls tp exp) st = let
        funVal = compExp funEnv (EFunc decls tp exp) funSt where
            funType = FuncType (argTypes decls) (typeToken tp)
            realVal = case funVal of Right v -> v
            (funEnv, funSt) = createVar fun funType env realVal st
    in funVal

compExp env (Call fexp exps) st = case compExp env fexp st of
    Right (FunVal args types funEnv funSt body tp) -> let
            argVals = map (\arg -> unright $ compExp env arg st) exps
            runSt = setValues (zip args argVals) funEnv funSt
        in compExp funEnv body runSt
            
        

{-
eval :: Exp -> Env -> State -> Either Exception Value
eval e en s = undefined


        EFunc decls tp exp -> if not $ allTyped decls
            then Left $ UntypedArgumentException e
            else case topExpType of
                Right (FuncType _ tp) -> let
                        (names, types) = evalTDecList decls
                    in Right $ FunVal names types en s exp tp
                    
                    
        ENFunc (Ident fun) decls tp exp -> if not $ allTyped decls
            then Left $ UntypedArgumentException e
            else case topExpType of
                Right (FuncType _ tp) -> let
                        (names, types) = evalTDecList decls
                        (fenv,fst1) = createVar fun (FuncType types tp) en s
                        funVal = let
                                fst2 = case setVar fun fenv funVal fst1 of
                                    Right fst -> fst
                            in FunVal names types fenv fst2 exp tp
                    in Right $ funVal
                       -- throw $ show fenv
        Call (Ident fun) exps -> case getVar fun en s of
            Left err -> Left err
            Right (FunVal names types fenv fst fexp ftp) ->
                case evalList exps en s of
                    Left err -> Left err
                    Right vals -> let
                            (funEnv, funSt) = createVars (names, types) fenv fst
                        in case setVars (zip names vals) funEnv funSt of
                            Left err -> Left err
                            Right funSt2 -> eval fexp funEnv funSt2
            Right _ -> Left $ Exception ("something horrible happened and" ++
                         "now i need to uninstall haskell")


evalList :: [Exp] -> Env -> State -> Either Exception [Value]
evalList [] _ _ = Right []
evalList (h:t) en st = case eval h en st of
    Left err -> Left err 
    Right val -> case evalList t en st of
        Left err -> Left err
        Right lst -> Right (val:lst)

-}














