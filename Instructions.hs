module Instructions where
import AbsHaskall
import Expressions
import Environment

type Prog = State -> Either Exception State

data CompileError =
    TypeCompileError TypingError
    | VarNotDeclared String Env
    | BadAssignment String VType Exp VType
    | BadLoopCondition Exp VType
    | CannotPrintError Exp VType
    | CannotReadError String VType

instance Show CompileError where
    show (TypeCompileError err) = show err

compileProgram pr env = compSt env pr


typeStm :: Stm -> Env -> Either CompileError (Env,Prog)
typeStm SPass env = Right (env, Right)


evalStmList :: Env -> [Stm] -> Either CompileError (Env,Prog)
evalStmList env [] = Right (env,\s -> Right s)
evalStmList env (stm:stmRest) = case compSt env stm of
    Left err -> Left err
    Right (newEnv, pr) -> case evalStmList newEnv stmRest of
        Left err -> Left err
        Right (fEnv, fPr) -> Right (fEnv, \s -> case pr s of
                    Left err -> Left err
                    Right s -> fPr s)

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
        Right (expTp, tpExp) -> let
                (loc,newEnv) = addToEnv var expTp env
            in Right (newEnv, \s -> case compExp newEnv tpExp s of
                Left err -> Left err
                Right v -> Right $ setInStore v loc s)

compSt env (SUnTDecl (Ident var) exp) =
    case typeExp exp env of
        Left err -> Left $ TypeCompileError err
        Right (expTp, tpExp) -> let
                (loc,newEnv) = addToEnv var expTp env
            in Right (newEnv, \s -> case compExp newEnv tpExp s of
                Left err -> Left err
                Right v -> Right $ setInStore v loc s)

compSt env (SBlock stmts) = evalStmList env stmts

compSt env (SWhile exp stms) = case typeExp exp env of
    Left err -> Left $ TypeCompileError err
    Right (expTp, tpExp) -> if expTp /= BoolType
        then Left $ BadLoopCondition exp expTp
        else case evalStmList env stms of
            Left err -> Left err
            Right (_, pr) -> let
                    loop s = case compExp env tpExp s of
                        Left err -> Left err
                        Right (BoolVal False) -> Right s
                        Right (BoolVal True )  -> case pr s of
                            Left err -> Left err
                            Right s2 -> loop s2
                in Right (env, loop)

compSt env (SIf exp stms1 stms2) = case typeExp exp env of
    Left err -> Left $ TypeCompileError err
    Right (expTp, tpExp) -> if expTp /= BoolType
        then Left $ BadLoopCondition exp expTp
        else case (evalStmList env stms1, evalStmList env stms2) of
            (Left err,_) -> Left err
            (_,Left err) -> Left err
            (Right (_,pr1), Right (_,pr2)) ->
                    Right (env, \s -> case compExp env tpExp s of
                        Left err -> Left err
                        Right (BoolVal False) -> pr1 s
                        Right (BoolVal True ) -> pr2 s)

compSt env (STPrint exp) = case typeExp exp env of
    Left err -> Left $ TypeCompileError err
    Right (expTp, tpExp) -> case expTp of
        StringType -> Right (env, \s -> case compExp env tpExp s of
                        Left err -> Left err
                        Right (StringVal str) -> Right $ pushToOut s str)
        IntType    -> Right (env, \s -> case compExp env tpExp s of
                        Left err -> Left err
                        Right (IntVal int) -> Right $ pushToOut s $ show int)
        _ -> Left $ CannotPrintError tpExp expTp

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
