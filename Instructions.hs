module Instructions where
import AbsHaskall
import Expressions
import PrintHaskall
import Environment


data CompileError =
    TypeCompileError TypingError
    | VarNotDeclared String Env
    | BadAssignment String VType Exp VType
    | BadLoopCondition Exp VType
    | CannotPrintError Exp VType
    | UndefinedProcError String Env
    | ProcArgTypesError String [VType] [VType]

instance Show CompileError where
    show (TypeCompileError err) = (show err)
    show (VarNotDeclared name env) = "compile error: variable " ++ name ++ 
        " is not defined in env:\n" ++ (show env)
    show (BadAssignment var tp exp expTp) = "compile error: cannot assign " ++
        "value of expression " ++ (printTree exp) ++ " of type " ++ (show tp)
        ++ " to variable " ++ var ++ " of type " ++ (show tp)
    show (BadLoopCondition exp tp) = "expression " ++ (printTree exp) ++
        " of type " ++ (show tp) ++ " cannot be a condition"
    show (CannotPrintError exp tp) = "compile error: cannot print expression"
        ++ (printTree exp) ++ " of type " ++ (show tp)
    show (UndefinedProcError pr env) = "compile error: cannot call undefined "
        ++ "procedure " ++ pr ++ " in env:\n" ++ (show env)
    show (ProcArgTypesError pr expTps actTps) = "compile error: cannot " ++
        "apply arguments of types " ++ (show actTps) ++ " to procedure " ++
        pr ++ " expecting types " ++ (show expTps)

compileProgram pr env = compSt env pr

sequenceProgs :: Prog -> Prog -> Prog
sequenceProgs pr1 pr2 = \s -> do
    s1 <- pr1 s
    case s1 of
        Left err -> return $ Left err
        Right s2 -> pr2 s2

evalStmList :: Env -> [Stm] -> Either CompileError (Env,Prog)
evalStmList env [] = Right (env,\s -> return $ Right s)
evalStmList env (stm:stmRest) = case compSt env stm of
    Left err -> Left err
    Right (newEnv, pr) -> case evalStmList newEnv stmRest of
        Left err -> Left err
        Right (fEnv, fPr) -> Right (fEnv, sequenceProgs pr fPr)

compSt :: Env -> Stm -> Either CompileError (Env,Prog)
compSt env SPass = Right (env, \s -> return $ Right s)
compSt env (SBlock stmts) = evalStmList env stmts
compSt env (STPrint exp) = case typeExp exp env of
    Left err -> Left $ TypeCompileError err
    Right (expTp, tpExp) -> case expTp of
        StringType -> Right (env, \s -> case compExp env tpExp s of
                        Left err -> return $ Left err
                        Right (StringVal str) -> do
                            putStr str
                            return $ Right s)
        IntType    -> Right (env, \s -> case compExp env tpExp s of
                        Left err -> return $ Left err
                        Right (IntVal int) -> do
                            putStr $ show int
                            return $ Right s)
        _ -> Left $ CannotPrintError tpExp expTp

compSt env (STDecl (Ident var) tpTok exp) =
    case lookupTypeDef env tpTok of
        Left err -> Left $ TypeCompileError err
        Right tp -> case expectType tp exp env of
            Left err -> Left $ TypeCompileError err
            Right (expTp, tpExp) -> let
                    (loc,newEnv) = addToEnv var expTp env
                in Right (newEnv, \s -> return $ case compExp newEnv tpExp s of
                    Left err -> Left err
                    Right v -> Right $ addToStore v loc s)

compSt env (SUnTDecl (Ident var) exp) =
    case typeExp exp env of
        Left err -> Left $ TypeCompileError err
        Right (expTp, tpExp) -> let
                (loc,newEnv) = addToEnv var expTp env
            in Right (newEnv, \s -> return $ case compExp newEnv tpExp s of
                Left err -> Left err
                Right v -> Right $ addToStore v loc s)

compSt env (SAssign (Ident var) exp) = case typeExp exp env of
    Left err -> Left $ TypeCompileError err
    Right (expTp, tpExp) -> case lookupEnv var env of
        Nothing -> Left $ VarNotDeclared var env
        Just (loc, tp) -> if tp /= expTp
            then Left $ BadAssignment var tp exp expTp
            else Right $ (env, \s -> return $ case compExp env tpExp s of
                Left err -> Left err
                Right v -> Right $ setInStore v loc s)

compSt env (SIf exp stms1 stms2) = case typeExp exp env of
    Left err -> Left $ TypeCompileError err
    Right (expTp, tpExp) -> if expTp /= BoolType
        then Left $ BadLoopCondition exp expTp
        else case (evalStmList env stms1, evalStmList env stms2) of
            (Left err,_) -> Left err
            (_,Left err) -> Left err
            (Right (_,pr1), Right (_,pr2)) ->
                    Right (env, \s -> case compExp env tpExp s of
                        Left err -> return $ Left err
                        Right (BoolVal True ) -> pr1 s
                        Right (BoolVal False) -> pr2 s)

compSt env (STAlias (Ident ntpt) tpt) =
    case lookupTypeDef env tpt of
        Left err -> Left $ TypeCompileError err
        Right tp -> Right (addType ntpt tp env, \s -> return $ Right s)

compSt env (SWhile exp stms) = case typeExp exp env of
    Left err -> Left $ TypeCompileError err
    Right (expTp, tpExp) -> if expTp /= BoolType
        then Left $ BadLoopCondition exp expTp
        else case evalStmList env stms of
            Left err -> Left err
            Right (_, pr) -> let
                    loop s = case compExp env tpExp s of
                        Left err -> return $ Left err
                        Right (BoolVal False) -> return  $ Right s
                        Right (BoolVal True ) -> sequenceProgs pr loop s
                in Right (env, loop)

compSt env (SProcDecl (Ident id) argts stm exp) =
    case argTypes env argts of
        Left err -> Left $ TypeCompileError err
        Right tps -> case addArguments argts env of
            Left err -> Left $ TypeCompileError err
            Right procEnv -> case compSt procEnv stm of
                Left err -> Left err
                Right (retEnv,cont) -> case typeExp exp env of
                    Left err -> Left $ TypeCompileError err
                    Right (expTp, tpExp) -> let -- case compExp env tpExp of
                            proc = Proc tps (argNames argts) cont (compExp retEnv tpExp) procEnv
                        in Right (addProc id proc env, \s -> return $ Right s)

compSt env (SProcRun (Ident id) exps) = case typeExpList exps env of
    Left err -> Left $ TypeCompileError err
    Right tps -> let (argTypes,tpArgs) = unzip tps in
        case lookupProc id env of
            Nothing -> Left $ UndefinedProcError id env
            Just proc -> if (pArgTypes proc) /= argTypes
                then Left $ ProcArgTypesError id (pArgTypes proc) argTypes
                else Right (env, \s -> case compExpList env exps s of
                    Left err -> return $ Left err
                    Right vals -> let
                            newSt = setValues (zip (pArgNames proc) vals) (pEnv proc) emptyState
                            runSt = StackedState newSt s
                        in do
                            s1 <- pCont proc runSt
                            case s1 of
                                Left err -> return $ Left err
                                Right (StackedState top bot) -> return $ Right bot )


-- XXX XXX XXX debug

compSt env STrace = Right (env, \s -> do
    putStrLn (show env)
    putStrLn (show s)
    return $ Right s)

