module Expressions where
import AbsHaskall
import Values
import Types
import Environment

-- DECLARATIONS

evalDecl :: Decl -> Env -> State -> Either String (Env, State)
evalDecl (VDecl (TDec (Ident var) t) e) en st = case eval e en st of
    Left err -> Left err
    Right val -> let
            newEnv = createVar var (typeToken t) en
            newSt  = setVar var newEnv val st
        in case newSt of
            Left err -> Left err
            Right st2 -> Right (newEnv, st2)

evalDeclList :: [Decl] -> Env -> State -> Either String (Env, State)
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
        else Left ((show e) ++ ", expected " ++ (show t) ++ ", got " ++ (show t1))

expect t1 e t2 en = case checkType t1 e en of
    Left er -> Left er
    Right tt -> Right t2

expect2 t1 t2 e1 e2 t3 en = case (checkType t1 e1 en, checkType t2 e2 en) of
    (Right _, Right _) -> Right t3
    (Left err, _) -> Left err
    (_, Left err) -> Left err

-- construction typings

typeExp :: Exp -> Env -> Either String VType
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
        then Left $ (show e1) ++ " of type " ++ (show t) ++ " as a condition"
        else case typeExp e2 en of
            Left err -> Left err
            Right t2 -> expect t2 e3 t2 en

typeExp (EVar (Ident var)) en = getVarType var en

typeExp (ELet decls e) en = case evalDeclList decls en emptyState of
    Left err -> Left err
    Right (newEnv, _) -> typeExp e newEnv

-- evaluations

eitherPair f e1 e2 = case (e1,e2) of (Right v1, Right v2) -> f v1 v2

eval :: Exp -> Env -> State -> Either String Value
eval e en s = case typeExp e en of
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


















