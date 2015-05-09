module Expressions where
import AbsHaskall
import Environment
import PrintHaskall

import Data.Either
import Data.List

-- DECLARATIONS

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
                    else throw $ "typing error: expected " ++ (show expT) ++
                                " but expression " ++ (show e) ++ " has type "
                                ++ (show t)

evalDeclList :: [Decl] -> Env -> State -> Either Exception (Env, State)
evalDeclList [] e s = Right (e,s)
evalDeclList (h:t) e s = case evalDecl h e s of
    Left err -> Left err
    Right (ne, ns) -> evalDeclList t ne ns


-- EXPRESSIONS


-- typing expectations

checkType t e en = case typeExp e en of
    Left er -> Left er
    Right t1 -> if t1 == t
        then Right t
        else throw ((show e) ++ ", expected " ++ (show t) ++ ", got " ++ (show t1))

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

typeExp (EEq e1 e2) en = expect2 IntType IntType e1 e2 BoolType en
typeExp (ELt e1 e2) en = expect2 IntType IntType e1 e2 BoolType en

typeExp (EIf e1 e2 e3) en = case typeExp e1 en of
    Left err -> Left err
    Right t  -> if t /= BoolType
        then throw $ (show e1) ++ " of type " ++ (show t) ++ " as a condition"
        else case typeExp e2 en of
            Left err -> Left err
            Right t2 -> expect t2 e3 t2 en

typeExp (EVar (Ident var)) en = getVarType var en

typeExp (ELet decls e) en = case evalDeclList decls en emptyState of
    Left err -> Left err
    Right (newEnv, _) -> typeExp e newEnv

typeExp (EFunc decls tp exp) en = if not $ allTyped decls
    then throw $ "derpy derp"
    else let
            (names, types) = evalTDecList decls
            (newEnv, newSt) = createVars (names, types) en emptyState
            t = typeToken tp
        in expect t exp (FuncType types t) newEnv

typeExp (Call (Ident fun) exps) en = case typeExps exps en of
    Left err -> Left err
    Right types -> case getVarType fun en of
        Left err -> Left err
        Right (FuncType tps tp) -> if tps /= types
            then throw $ "cannot apply arguments " ++ (show exps) ++
                        " of types " ++ (show types) ++ " to function " ++
                        fun ++ " of type " ++ (show (FuncType tps tp))
            else Right tp

typeExps :: [Exp] -> Env -> Either Exception [VType]
typeExps exps en = let types = map (flip typeExp en) exps in
    case lefts types of
        [] -> Right $ rights types
        lst -> throw (intercalate ", " (map show lst))


-- evaluations

eitherPair f e1 e2 = case (e1,e2) of (Right v1, Right v2) -> f v1 v2

eval :: Exp -> Env -> State -> Either Exception Value
eval e en s = let topExpType = typeExp e en in case topExpType of
    Left err -> Left err
    Right _ -> case e of
        ETrue  -> Right $ BoolVal True
        EFalse -> Right $ BoolVal False
        EInt i -> Right $ IntVal i
        EAdd e1 e2 -> Right $ eitherPair valAdd (eval e1 en s) (eval e2 en s)
        ESub e1 e2 -> Right $ eitherPair valSub (eval e1 en s) (eval e2 en s)
        EMul e1 e2 -> Right $ eitherPair valMul (eval e1 en s) (eval e2 en s)
        EEq e1 e2  -> Right $ eitherPair valIntEq (eval e1 en s) (eval e2 en s)
        ELt e1 e2  -> Right $ eitherPair valLt (eval e1 en s) (eval e2 en s)
        EIf e1 e2 e3 -> case eval e1 en s of
            Right (BoolVal True)  -> eval e2 en s
            Right (BoolVal False) -> eval e3 en s
        EVar (Ident var) -> getVar var en s
        ELet decls exp -> case evalDeclList decls en s of
            Left err -> Left err
            Right (ne, ns) -> eval exp ne ns
        EFunc decls tp exp -> if not $ allTyped decls
            then throw $ "untyped arguments in " ++ (printTree e) ++ (show decls)
            else let
                    (names, types) = evalTDecList decls
                    func = case topExpType of
                        Right (FuncType _ tp) -> FunVal names types en exp tp
                in Right func
        Call (Ident fun) exps -> case getVar fun en s of
            Left err -> Left err
            Right (FunVal names types fenv fexp ftp) ->
                case evalList exps en s of
                    Left err -> Left err
                    Right vals -> let
                            (funEnv, funSt) = createVars (names, types) fenv s
                        in case setVars (zip names vals) funEnv funSt of
                            Left err -> Left err
                            Right funSt2 -> eval fexp funEnv funSt2

evalList :: [Exp] -> Env -> State -> Either Exception [Value]
evalList [] _ _ = Right []
evalList (h:t) en st = case eval h en st of
    Left err -> Left err 
    Right val -> case evalList t en st of
        Left err -> Left err
        Right lst -> Right (val:lst)
















