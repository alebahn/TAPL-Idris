module Main

import Data.Fuel

import Parser
import Eval

%default total

loop : Fuel -> IO ()
loop Dry = pure ()
loop (More fuel) = do
  putStr "In "
  inputStr <- getLine
  case parse inputStr of
       Left error => do
         putStrLn ("Error " ++ error)
       Right (size ** (context, term)) => do
         case getType context term of
              Left error => putStrLn ("Type Error " ++ error)
              Right _ => do
                let norm = totalEval term fuel
                putStrLn ("Out " ++ show context norm)
  loop fuel

covering
main : IO ()
main = loop forever
