module Instructions where
import AbsHaskall
import Expressions
import PrintHaskall
import Environment

type Prog = State -> Either Exception State

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
    case lookupTypeDef env tpTok of
        Left err -> Left $ TypeCompileError err
        Right tp -> case expectType tp exp env of
            Left err -> Left $ TypeCompileError err
            Right (expTp, tpExp) -> let
                    (loc,newEnv) = addToEnv var expTp env
                in Right (newEnv, \s -> case compExp newEnv tpExp s of
                    Left err -> Left err
                    Right v -> Right $ addToStore v loc s)

compSt env (SUnTDecl (Ident var) exp) =
    case typeExp exp env of
        Left err -> Left $ TypeCompileError err
        Right (expTp, tpExp) -> let
                (loc,newEnv) = addToEnv var expTp env
            in Right (newEnv, \s -> case compExp newEnv tpExp s of
                Left err -> Left err
                Right v -> Right $ addToStore v loc s)

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
                        Right (BoolVal True ) -> pr1 s
                        Right (BoolVal False) -> pr2 s)

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

compSt env (STAlias (Ident ntpt) tpt) =
    case lookupTypeDef env tpt of
        Left err -> Left $ TypeCompileError err
        Right tp -> Right (addType ntpt tp env, \s -> Right s)

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
                        in Right (addProc id proc env, \s -> Right s)

compSt env (SProcRun (Ident id) exps) = case typeExpList exps env of
    Left err -> Left $ TypeCompileError err
    Right tps -> let (argTypes,tpArgs) = unzip tps in
        case lookupProc id env of
            Nothing -> Left $ UndefinedProcError id env
            Just proc -> if (pArgTypes proc) /= argTypes
                then Left $ ProcArgTypesError id (pArgTypes proc) argTypes
                else Right (env, \s -> case compExpList (pEnv proc) exps s of
                    Left err -> Left err
                    Right vals -> let
                            newSt = setValues (zip (pArgNames proc) vals) (pEnv proc) emptyState
                            runSt = StackedState newSt s
                        in case pCont proc $ runSt of
                            Left err -> Left err
                            Right (StackedState top bot) -> Right bot )

