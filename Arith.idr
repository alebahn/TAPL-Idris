module Main

import Data.Fuel

import ArithParser
import ArithEval

%default total

loop : Fuel -> IO ()
loop Dry = pure ()
loop (More fuel) = do
  putStr "In "
  inputStr <- getLine
  case parse inputStr of
       Left error => do
         putStrLn ("Error " ++ error)
         loop fuel
       Right term => do
         let norm = eval term
         putStrLn ("Out " ++ show norm)
         loop fuel

covering
main : IO ()
main = loop forever
