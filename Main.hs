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

parseIt input = case pProgram $ myLexer input of
    Bad err -> err
    Ok prog -> case prog of
        Eval exp -> case compileExpression exp emptyEnv of
            Right v -> case v emptyState of
                Left err -> show err
                Right v -> show v
            Left er -> show er
        Prog stm -> case compileProgram stm emptyEnv of
            Right (_,v) -> case v emptyState of
                Left err -> show err
                Right s  -> output s
            Left er -> show er

main :: IO ()
main = do
    args <- getArgs
    input <- case args of
        [] -> getContents
        f:_ -> readFile f
    putStrLn $ parseIt input
    return ()
