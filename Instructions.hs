module Instructions where
import AbsHaskall
import Expressions
import Environment

type Prog = State -> Either Exception State

data CompileError =
    TypeCompileError TypingError
    | VarNotDeclared String Env
    | BadAssignment String VType Exp VType

instance Show CompileError where
    show (TypeCompileError err) = show err

typeStm :: Stm -> Env -> Either CompileError (Env,Prog)
typeStm SPass env = Right (env, Right)


compSt :: Env -> Stm -> Either CompileError (Env,Prog)
compSt env SPass = Right $ (env, \s -> Right s)
compSt env (SAssign (Ident var) exp) = case typeExp exp env of
    Left err -> Left $ TypeCompileError err
    Right (expTp, tpExp) -> case lookupEnv var env of
        Nothing -> Left $ VarNotDeclared var env
        Just (loc, tp) -> if tp /= expTp
            then Left $ BadAssignment var tp exp expTp
            else Right $ (env, \s -> case compExp env tpExp s of
                Left err -> Left err
                Right v -> Right $ setInStore v loc s)

compSt env (STDecl (Ident var) tpTok exp) =
    case expectType (typeToken tpTok) exp env of
        Left err -> Left $ TypeCompileError err
        Right (expTp, tpExp) -> undefined

{-
evalStm :: Env -> Stm -> State -> Either Exception State

evalStm en SPass s = Right s
evalStm en (SAssign (Ident var) exp) s = case eval exp en s of
    Left err -> Left err
    Right val -> setVar var en val s

evalStm en (SIf exp stm1 stm2) s = case typeExp exp en of
    Left err -> Left err
    Right t -> if t /= BoolType
        then Left $ ConditionException exp t
        else case eval exp en s of
            Left err -> Left err
            Right val -> case val of
                BoolVal True  -> evalStm en stm1 s
                BoolVal False -> evalStm en stm2 s

evalStm en (SWhile exp stm) s = case typeExp exp en of
    Left err -> Left err
    Right t -> if t /= BoolType
        then Left $ ConditionException exp t
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

-}
