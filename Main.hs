module Main where

import LexHaskall
import ParHaskall
import SkelHaskall
import PrintHaskall
import AbsHaskall
import ErrM

import Expressions
import Environment

import Data.Map (empty)

parseIt input = case pProgram $ myLexer input of
    Bad err -> err
    Ok prog -> case prog of
        Eval exp -> case eval exp emptyEnv empty of
            Right v -> show v
            Left er -> er
        Prog stm -> "not implemented yet"

main :: IO ()
main = do
    input <- getContents
    putStrLn $ parseIt input
    return ()
