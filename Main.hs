module Main where

import System.Environment

import LexHaskall
import ParHaskall
import SkelHaskall
import PrintHaskall
import AbsHaskall
import ErrM

import Expressions
import Environment
import Instructions

import Data.Map (empty)

parseIt :: String -> IO ()
parseIt input = case pProgram $ myLexer input of
    Bad err -> putStrLn $ show err
    Ok prog -> case prog of
        Eval exp -> case compileExpression exp emptyEnv of
            Right v -> case v emptyState of
                Left err -> putStrLn $ show err
                Right v -> putStrLn $ show v
            Left er -> putStrLn $ show er
        Prog stm -> case compileProgram stm emptyEnv of
            Right (_,v) -> do
                result <- v emptyState
                case result of
                    Left err -> putStrLn $ show err
                    Right _  -> return ()
            Left er -> putStrLn $ show er

main :: IO ()
main = do
    args <- getArgs
    input <- case args of
        [] -> getContents
        f:_ -> readFile f
    parseIt input
    return ()
