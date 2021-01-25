module ArithParser

import Data.Strings
import Data.Vect
import Decidable.Equality
import Control.WellFounded
import Data.Nat

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

parseTermStep : (tokens : List Token) -> ((tokens' : List Token) -> (tokens' `Smaller` tokens) -> Either String (Term, (resid : List Token ** resid `Smaller` tokens'))) -> Either String (Term, (resid : List Token ** resid `Smaller` tokens))
parseTermStep (TTrue :: xs) _ = Right (TmTrue, (xs ** lteRefl))
parseTermStep (TFalse :: xs) _ = Right (TmFalse, (xs ** lteRefl))
parseTermStep (TZero :: xs) _ = Right (TmZero, (xs ** lteRefl))
parseTermStep (TSucc :: xs) f = do (term, (resid ** prf)) <- f xs lteRefl
                                   pure (TmSucc term, (resid ** lteSuccRight prf))
parseTermStep (TPred :: xs) f = do (term, (resid ** prf)) <- f xs lteRefl
                                   pure (TmPred term, (resid ** lteSuccRight prf))
parseTermStep (TIszero :: xs) f = do (term, (resid ** prf)) <- f xs lteRefl
                                     pure (TmIszero term, (resid ** lteSuccRight prf))
parseTermStep (TIf :: xs) f = do (guard, (gResid ** gPrf)) <- f xs lteRefl
                                 (thenTerm, (tResid ** tPrf)) <- f gResid (lteSuccRight gPrf)
                                 (elseTerm, (eResid ** ePrf)) <- f tResid (lteTransitive (lteSuccRight tPrf) (lteSuccRight gPrf))
                                 pure (TmIf guard thenTerm elseTerm, (eResid ** (lteTransitive (lteSuccRight ePrf) (lteTransitive (lteSuccRight tPrf) (lteSuccRight gPrf)))))
parseTermStep _ _ = Left "Invalid Term"

parseTerm : (tokens : List Token) -> Either String Term
parseTerm tokens = do (term, (resid ** _)) <- the (Either String (Term, (resid : List Token ** resid `Smaller` tokens))) (sizeInd parseTermStep tokens)
                      if (length resid == 0) then pure term
                                             else Left "Extra tokens at end of term"

export
parse : String -> Either String Term
parse str = do
  tokens <- tokenize str
  parseTerm tokens
