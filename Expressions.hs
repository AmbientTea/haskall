module Expressions where
import AbsHaskall
import Values
import Types
import Environment


checkType t e = case typeExp e of
    Left er -> Left er
    Right t1 -> if t1 == t
        then Right t
        else Left ((show e) ++ ", expected " ++ (show t) ++ ", got " ++ (show t1))

expect t1 e t2 = case checkType t1 e of
    Left er -> Left er
    Right tt -> Right t2

expect2 t1 t2 e1 e2 t3 = case (checkType t1 e1, checkType t2 e2) of
    (Right _, Right _) -> Right t3
    (Left err, _) -> Left err
    (_, Left err) -> Left err

typeExp :: Exp -> Either String VType
typeExp ETrue    = Right BoolType
typeExp EFalse   = Right BoolType
typeExp (EInt _) = Right IntType

typeExp (EMul e1 e2) = expect2 IntType IntType e1 e2 IntType
typeExp (ESub e1 e2) = expect2 IntType IntType e1 e2 IntType
typeExp (EAdd e1 e2) = expect2 IntType IntType e1 e2 IntType

typeExp (EEq e1 e2) = expect2 IntType IntType e1 e2 BoolType
typeExp (ELt e1 e2) = expect2 IntType IntType e1 e2 BoolType

typeExp (EIf e1 e2 e3) = case typeExp e1 of
    Left err -> Left err
    Right t  -> if t /= BoolType
        then Left $ (show e1) ++ " of type " ++ (show t) ++ " as a condition"
        else case typeExp e2 of
            Left err -> Left err
            Right t2 -> expect t2 e3 t2

eitherPair f e1 e2 = case (e1,e2) of (Right v1, Right v2) -> f v1 v2

eval :: Exp -> Either String Value
eval e = case typeExp e of
    Left err -> Left err
    Right _ -> case e of
        ETrue  -> Right $ BoolVal True
        EFalse -> Right $ BoolVal False
        EInt i -> Right $ IntVal i
        EAdd e1 e2 -> Right $ eitherPair valAdd (eval e1) (eval e2)
        ESub e1 e2 -> Right $ eitherPair valSub (eval e1) (eval e2)
        EMul e1 e2 -> Right $ eitherPair valMul (eval e1) (eval e2)
        EEq e1 e2  -> Right $ eitherPair valIntEq (eval e1) (eval e2)
        ELt e1 e2  -> Right $ eitherPair valLt (eval e1) (eval e2)
        EIf e1 e2 e3 -> case eval e1 of
            Right (BoolVal True)  -> eval e2
            Right (BoolVal False) -> eval e3



















