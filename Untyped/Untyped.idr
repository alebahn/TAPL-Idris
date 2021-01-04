module Main

import Data.Fuel

import Parser
import Eval

%default total

--we are calling eval which calls a touring complete language. this will never be total (I guess we could prove productivity, but whatever)
covering
loop : Fuel -> IO ()
loop Dry = pure ()
loop (More fuel) = do
  putStr "In "
  inputStr <- getLine
  case parse inputStr of
       Left error => do
         putStrLn ("Error " ++ error)
         loop fuel
       Right (size ** (context, term)) => do
         --putStrLn ("Echo " ++ show context term)
         let norm = eval term
         putStrLn ("Out " ++ show context norm)
         loop fuel

covering
main : IO ()
main = loop forever
