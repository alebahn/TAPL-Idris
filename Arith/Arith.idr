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
         let norm = bigStepEval term
         case norm of
              Nothing => putStrLn "Eval Error"
              (Just val) => putStrLn ("Out " ++ show val)
         loop fuel

covering
main : IO ()
main = loop forever
