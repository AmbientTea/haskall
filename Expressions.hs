module Expressions where
import AbsHaskall
import Environment
import PrintHaskall

import Data.Either
import Data.List

-- DECLARATIONS

-- function arguments
addArgument (TArgDec (Ident arg) tp) env st =
    createEmptyVar arg (typeToken tp) env st

addArguments [] env st = (env,st)
addArguments (arg:rest) env st = let (newEnv, newSt) = addArgument arg env st
    in addArguments rest newEnv newSt

argTypes args = map (\(TArgDec _ tp) -> typeToken tp) args
argNames args = map (\(TArgDec (Ident arg) _) -> arg) args

{-
-- typed
allTyped ((TDec _ _):t) = allTyped t
allTyped ((UnTDec _):t) = False
allTyped [] = True

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
            
        


eval :: Exp -> Env -> State -> Either Exception Value
eval e en s = undefined
{-

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
-}

evalList :: [Exp] -> Env -> State -> Either Exception [Value]
evalList [] _ _ = Right []
evalList (h:t) en st = case eval h en st of
    Left err -> Left err 
    Right val -> case evalList t en st of
        Left err -> Left err
        Right lst -> Right (val:lst)
















