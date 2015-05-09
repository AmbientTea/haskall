module Main where

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
        Eval exp -> case eval exp emptyEnv emptyState of
            Right v -> show v
            Left er -> show er
        Prog stm -> case evalStm emptyEnv stm emptyState of
            Right s -> show s
            Left er -> show er

main :: IO ()
main = do
    input <- getContents
    putStrLn $ parseIt input
    return ()
