module ArithParser

import Data.Strings
import Data.Vect
import Decidable.Equality

import ArithTokens

%default total

public export
data Term = TmTrue
          | TmFalse
          | TmIf Term Term Term
          | TmZero
          | TmSucc Term
          | TmPred Term
          | TmIszero Term

export
Show Term where
  show TmTrue = "true"
  show TmFalse = "false"
  show (TmIf g t e) = "if " ++ (show g) ++ " then " ++ (show t) ++ " else " ++ (show e)
  show TmZero = "0"
  show (TmSucc t) = "succ " ++ (show t)
  show (TmPred t) = "pred " ++ (show t)
  show (TmIszero t) = "iszero " ++ (show t)

||| A List that is a smaller list of the given list
data SubList : List t -> Type where
  ||| Remove only the first element to form the SubList
  SubTail : (tail : List t) -> SubList (head :: tail)
  ||| Ommit an additional element from the List
  SubLess : (sub : SubList tail) -> SubList (head :: tail)

subLessHelp : Functor f =>  f (a, SubList tail) -> f (a, SubList (head :: tail))
subLessHelp = map (\(value, subList) => (value, SubLess subList))

parseMap : Functor f => (func : a -> b) -> f (a, SubList list) -> f (b, SubList list)
parseMap func = map (\(input, subList) => (func input, subList))

parseTerm : (tokens : List Token) -> Either String (Term, SubList tokens)
parseTerm (TTrue :: xs) = Right (TmTrue, SubTail xs)
parseTerm (TFalse :: xs) = Right (TmFalse, SubTail xs)
parseTerm (TZero :: xs) = Right (TmZero, SubTail xs)
parseTerm (TSucc :: xs) = do (term, remaining) <- parseTerm xs
                             pure (TmSucc term, SubLess remaining)
parseTerm (TPred :: xs) = do (term, remaining) <- parseTerm xs
                             pure (TmPred term, SubLess remaining)
parseTerm (TIszero :: xs) = do (term, remaining) <- parseTerm xs
                               pure (TmIszero term, SubLess remaining)
parseTerm (TIf :: xs) = do (guard, gRemaining) <- parseTerm xs
                           (thenTerm, tRemaining) <- lookForThen gRemaining
                           (elseTerm, eRemaining) <- lookForElse tRemaining
                           pure (TmIf guard thenTerm elseTerm, SubLess eRemaining)

                           where
                             lookForThen : {0 subInput : List Token} -> SubList subInput -> Either String (Term, SubList subInput)
                             lookForThen (SubLess sub) = subLessHelp (lookForThen sub)
                             lookForThen (SubTail (TThen :: tail)) = subLessHelp $ subLessHelp $ parseTerm tail
                             lookForThen (SubTail _) = Left "Expected then after if guard"

                             lookForElse : {0 subInput : List Token} -> SubList subInput -> Either String (Term, SubList subInput)
                             lookForElse (SubLess sub) = subLessHelp (lookForElse sub)
                             lookForElse (SubTail (TElse :: tail)) = subLessHelp $ subLessHelp $ parseTerm tail
                             lookForElse (SubTail _) = Left "Expected else after then"
parseTerm _ = Left "Invalid Term"

export
parse : String -> Either String Term
parse str = do
  tokens <- tokenize str
  (term, remaining) <- parseTerm tokens
  ensureEmpty term remaining
  where
    ||| count any remaining amount as a parse error
    ensureEmpty : Term -> SubList tokens -> Either String Term
    ensureEmpty term (SubTail []) = Right term
    ensureEmpty term (SubLess subList) = ensureEmpty term subList
    ensureEmpty _ _ = Left "Extra tokens at end of term"
