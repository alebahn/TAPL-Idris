module Main

import Data.Fuel
import Data.Vect

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
       Right (0 ** ([], term)) => do
         case getType [] term of
              Left error => putStrLn ("Type Error " ++ error)
              Right (_ ** hasType) => do
                let norm = bigStepEvalTerm term hasType
                putStrLn ("Out " ++ show [] norm)
       Right (_ ** (_, term)) => do
         putStrLn "Only closed terms are evaluated"
  loop fuel

covering
main : IO ()
main = loop forever
