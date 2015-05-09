module Instructions where
import AbsHaskall
import Expressions
import Environment

evalStm :: Env -> Stm -> State -> Either Exception State

evalStm en SPass s = Right s
evalStm en (SAssign (Ident var) exp) s = case eval exp en s of
    Left err -> Left err
    Right val -> setVar var en val s

evalStm en (SIf exp stm1 stm2) s = case typeExp exp en of
    Left err -> Left err
    Right t -> if t /= BoolType
        then throw $ "expression " ++ (show exp) ++ " of type " ++
                    (show t) ++ " as a condition"
        else case eval exp en s of
            Left err -> Left err
            Right val -> case val of
                BoolVal True  -> evalStm en stm1 s
                BoolVal False -> evalStm en stm2 s

evalStm en (SWhile exp stm) s = case typeExp exp en of
    Left err -> Left err
    Right t -> if t /= BoolType
        then throw $ "expression " ++ (show exp) ++ " of type " ++
                    (show t) ++ " as a loop condition"
        else case eval exp en s of
            Left err -> Left err
            Right val -> case val of
                BoolVal True  -> case evalStm en stm s of
                    Left err -> Left err
                    Right s2 -> evalStm en (SWhile exp stm) s2
                BoolVal False -> Right s

evalStm en (SBlock decls stms) s = case evalDeclList decls en s of
    Left err -> Left err
    Right (ne, ns) -> evalStmList ne stms ns


evalStmList :: Env -> [Stm] -> State -> Either Exception State
evalStmList en [] s = Right s
evalStmList en (h:t) s = case evalStm en h s of
    Left err -> Left err
    Right s2 -> evalStmList en t s2


