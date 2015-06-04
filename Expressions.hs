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
addArgument (TArgDec (Ident arg) tp) env st =
    createEmptyVar arg (typeToken tp) env st

addArguments [] env st = (env,st)
addArguments (arg:rest) env st = let (newEnv, newSt) = addArgument arg env st
    in addArguments rest newEnv newSt

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

{-
typeExp (ELt e1 e2) env = case expectType IntType e1 env of
    Left err -> Left err
    Right (_, exp1) -> case expectType IntType e2 env of
        Left err -> Left err
        Right (_, exp2) -> Right (BoolType, ELt exp1 exp2)
-}

typeExp (ELt e1 e2) env = typeBoth e1 e2 IntType IntType BoolType ELt env
typeExp (EEq e1 e2) env = case (typeExp e1 env, typeExp e2 env) of
    (Right (type1, exp1), Right (type2, exp2)) -> case (type1,type2) of
        (IntType,IntType)   -> Right (BoolType, EEq exp1 exp2)
        (BoolType,BoolType) -> Right (BoolType, EEq exp1 exp2)
        _ -> Left $ EqTypingError (EEq e1 e2) type1 type2
    (Left err, _) -> Left err
    (_, Left err) -> Left err

typeExp (EFunc args tp exp) env = let
        (funEnv, funSt) = addArguments args env emptyState
        eType = typeToken tp
    in case typeExp exp funEnv of
        Left err -> Left err
        Right (funType, typedExp) -> if funType == eType
            then Right (FuncType (argTypes args) eType, EFunc args tp typedExp)
            else Left $ FunctionTypeError (EFunc args tp exp) eType funType

typeExp (ENFunc (Ident fun) args tp exp) env = let
        atypes = argTypes args
        funEnv = addToEnv fun 0 (FuncType atypes (typeToken tp)) env
    in case typeExp (EFunc args tp exp) env of
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
                letEnv = addToEnv var 0 (typeToken varTP) env
            in case typeExp (ELet decls exp) letEnv of
                Left err -> Left err
                Right (letTp, ELet fdecls fexp) ->
                    Right $ (letTp, ELet (tpDecl:fdecls) fexp)

{-
compExp env (EFunc decls tp exp) st = let
        (funEnv, funSt) = addArguments decls env st
    in Right $ FunVal (argNames decls) (argTypes decls) funEnv
                                                    funSt exp (typeToken tp)
-}
{-
typeExp (EFunc args tp exp) env = let
        argTypes = typeExpList args env
    in if argTypes
  -}  

typeExp (EAdd e1 e2) env = typeBoth e1 e2 IntType IntType IntType EAdd env
typeExp (ESub e1 e2) env = typeBoth e1 e2 IntType IntType IntType ESub env
typeExp (EMul e1 e2) env = typeBoth e1 e2 IntType IntType IntType EMul env
typeExp (EDiv e1 e2) env = typeBoth e1 e2 IntType IntType IntType EDiv env

typeExp e env = Right $ case e of
    ETrue  -> (BoolType, e)
    EFalse -> (BoolType, e)
    EInt i -> (IntType, e)
    EVar (Ident var) -> (getType var env, e)
    




{-
-- typed

evalTDecl (TDec (Ident var) tp) = (var, typeToken tp)

evalTDecList :: [TDecl] -> ([String], [VType])
evalTDecList l = unzip $ map evalTDecl l

-- variables
evalDecl :: Decl -> Env -> State -> Either Exception (Env, State)

evalDecl (VDecl decl e) en st = case eval e en st of
    Left err -> Left err
    Right val -> let
                t = typeValue val
                (var, expT) = case decl of
                    TDec (Ident vr) ext -> (vr, typeToken ext)
                    UnTDec (Ident vr) -> (vr, t)
                (newEnv, newSt) = createVar var t en st
                newSt2  = setVar var newEnv val newSt
            in case newSt2 of
                Left err -> Left err
                Right st2 -> if t == expT
                    then Right (newEnv, st2)
                    else Left $ TypingException expT t e

evalDeclList :: [Decl] -> Env -> State -> Either Exception (Env, State)
evalDeclList [] e s = Right (e,s)
evalDeclList (h:t) e s = case evalDecl h e s of
    Left err -> Left err
    Right (ne, ns) -> evalDeclList t ne ns
-}

-- 

-- EXPRESSIONS


-- typing expectations
{-
checkType t e en = case typeExp e en of
    Left er -> Left er
    Right t1 -> if t1 == t
        then Right t
        else Left $ TypingException t t1 e
        -- else throw ((show e) ++ ", expwefwefected " ++ (show t) ++ ", got " ++ (show t1))

expect t1 e t2 en = case checkType t1 e en of
    Left er -> Left er
    Right tt -> Right t2

expect2 t1 t2 e1 e2 t3 en = case (checkType t1 e1 en, checkType t2 e2 en) of
    (Right _, Right _) -> Right t3
    (Left err, _) -> Left err
    (_, Left err) -> Left err

-- construction typings

typeExp :: Exp -> Env -> Either Exception VType
typeExp ETrue  en   = Right BoolType
typeExp EFalse  en  = Right BoolType
typeExp (EInt _) en = Right IntType

typeExp (EMul e1 e2) en = expect2 IntType IntType e1 e2 IntType en
typeExp (ESub e1 e2) en = expect2 IntType IntType e1 e2 IntType en
typeExp (EAdd e1 e2) en = expect2 IntType IntType e1 e2 IntType en
typeExp (EDiv e1 e2) en = expect2 IntType IntType e1 e2 IntType en

typeExp (EEq e1 e2) en = expect2 IntType IntType e1 e2 BoolType en
typeExp (ELt e1 e2) en = expect2 IntType IntType e1 e2 BoolType en

typeExp (EIf e1 e2 e3) en = case typeExp e1 en of
    Left err -> Left err
    Right t  -> if t /= BoolType
        then Left $ ConditionException e1 t
        else case typeExp e2 en of
            Left err -> Left err
            Right t2 -> expect t2 e3 t2 en

typeExp (EVar (Ident var)) en = getVarType var en

typeExp (ELet decls e) en = undefined

{-case evalDeclList decls en emptyState of
    Left err -> Left err
    Right (newEnv, _) -> typeExp e newEnv -}

typeExp (EFunc decls tp exp) en = if not $ allTyped decls
    then Left $ UntypedArgumentException (EFunc decls tp exp) 
    else let
            (names, types) = evalTDecList decls
            (newEnv, newSt) = createVars (names, types) en emptyState
            t = typeToken tp
        in expect t exp (FuncType types t) newEnv

typeExp (ENFunc (Ident fun) decls tp exp) en = if not $ allTyped decls
    then Left $ UntypedArgumentException (EFunc decls tp exp) 
    else let
            (names, types) = evalTDecList decls
            t = typeToken tp
            funType = FuncType types t
            (newEnv, newSt) = createVars (names, types) en emptyState
            (newEnv2, newSt2) = createVar fun funType newEnv newSt
        in expect t exp funType newEnv2
           -- Left $ Exception $ show $ expect t exp funType newEnv2
           -- Left $ Exception (show newEnv2)

typeExp (Call (Ident fun) exps) en = case typeExps exps en of
    Left err -> Left err
    Right types -> case getVarType fun en of
        Left err -> Left err
        Right (FuncType tps tp) -> if tps /= types
            then Left $ BadArgumentsException exps types fun (FuncType tps tp)
            else Right tp

typeExps :: [Exp] -> Env -> Either Exception [VType]
typeExps exps en = let types = map (flip typeExp en) exps in
    case lefts types of
        [] -> Right $ rights types
        lst -> throw (intercalate "\n" (map show lst))

-}
-- evaluations

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
        (funEnv, funSt) = addArguments decls env st
    in Right $ FunVal (argNames decls) (argTypes decls) funEnv
                                                    funSt exp (typeToken tp)

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














