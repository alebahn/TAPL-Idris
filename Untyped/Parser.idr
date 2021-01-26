module Parser

import Data.Strings
import Data.Vect
import Decidable.Equality
import Data.Nat
import Control.WellFounded

import Tokens

%default total

public export
data Term : Nat -> Type where
  TmVar : Fin n -> Term n
  TmAbs : String -> Term (S n) -> Term n
  TmApp : Term n -> Term n -> Term n

liftTerm : Term n -> n `LTE` m -> Term m
liftTerm (TmVar k) lte = TmVar (weakenLTE k lte)
liftTerm (TmAbs name body) lte = TmAbs name (liftTerm body (LTESucc lte))
liftTerm (TmApp x y) lte = TmApp (liftTerm x lte) (liftTerm y lte)

Context : Nat ->Type
Context n = Vect n String

showPrec : Prec -> Context n -> Term n -> String
showPrec _    context (TmVar j) = index j context
showPrec d context (TmAbs name body) = showParens (d > Equal) ("\\" ++ name ++ ". " ++ showPrec Equal (name :: context) body)
showPrec d context (TmApp x y) = showParens (d >= App) (showPrec Backtick context x ++ " " ++ showPrec App context y)

export
show : Context n -> Term n -> String
show context term = showPrec Open context term

ParseResult : Nat -> List Token -> Type
ParseResult n tokens = ((size : Nat ** (n `LTE` size, Context size, Term size)), (resid : List Token ** resid `Smaller` tokens))

findInContextOrAdd : String -> Context n -> Either (Context (S n)) (Fin n)
findInContextOrAdd name context = case elemIndex name context of
                                       Nothing => Left $ rewrite plusCommutative 1 n in (context ++ [name])
                                       (Just ind) => Right ind

mutual
  parseRecur : {n : Nat} -> (context : Context n) -> (term : Term n) -> (subTokens : List Token) -> (subTokensSmaller : subTokens `Smaller` tokens) -> (0 acc : SizeAccessible tokens) -> ParseResult n tokens
  parseRecur context term subTokens subTokensSmaller (Access acc) = case parseTerm context subTokens (acc subTokens subTokensSmaller) of
                                                                         (Left _) => ((_ ** (lteRefl, context, term)), (subTokens ** subTokensSmaller))
                                                                         (Right ((size ** (lte, context', term2)), (resid ** residSmaller))) => let newApp = TmApp (liftTerm term lte) term2
                                                                                                                                                    ((size' ** (lte', contextTerm)), (resid' ** residSmaller')) = parseRecur context' newApp resid {tokens=subTokens} residSmaller (acc subTokens subTokensSmaller) in
                                                                                                                                                    ((size' ** (lteTransitive lte lte', contextTerm)), (resid' ** lteTransitive (lteSuccRight residSmaller') subTokensSmaller))

  parseWhole : {n : Nat} -> (context: Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (ParseResult n tokens)
  parseWhole context tokens acc = do ((size ** (lte, context', term)), (resid ** residSmaller)) <- parseTerm context tokens acc
                                     let ((size' ** (lte', contextTerm)), (resid' ** residSmaller')) = parseRecur context' term resid {tokens} residSmaller acc
                                     pure ((size' ** (lteTransitive lte lte', contextTerm)), (resid' ** residSmaller'))

  parseTerm : {n : Nat} -> (context : Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (ParseResult n tokens)
  parseTerm context ((TVar name) :: xs) _ = case findInContextOrAdd name context of
                                                 (Left newContext) => Right ((S n ** (lteSuccRight lteRefl, newContext, TmVar last)), (xs ** lteRefl))
                                                 (Right index) => Right ((n ** (lteRefl, context, TmVar index)), (xs ** lteRefl))
  parseTerm context (TLambda :: (TVar name) :: TDot :: xs) (Access acc) = do (bodyData, (resid ** residSmaller)) <- parseWhole (name :: context) xs (acc xs (lteSuccRight $ lteSuccRight $ lteRefl))
                                                                             pure (makeApp name bodyData, (resid ** lteSuccRight $ lteSuccRight $ lteSuccRight $ residSmaller))
                                                                             where
                                                                               lteSuccZeroImpossible : LTE (S n) 0 -> Void
                                                                               lteSuccZeroImpossible LTEZero impossible
                                                                               lteSuccZeroImpossible (LTESucc x) impossible

                                                                               makeApp : String -> (size : Nat ** (LTE (S n) size, (Vect size String, Term size))) -> (size : Nat ** (LTE n size, (Vect size String, Term size)))
                                                                               makeApp name (0 ** (lte, _)) = void (lteSuccZeroImpossible lte)
                                                                               makeApp name ((S k) ** (LTESucc lte, (_ :: context), body)) = (k ** (lte, context, TmAbs name body))
  parseTerm context (TLParen :: xs) (Access acc) = do (termData, ((TRParen :: resid) ** residSmaller)) <- parseWhole context xs (acc xs lteRefl)
                                                        | _ => Left "Missing right parenthesis"
                                                      pure (termData, (resid ** lteSuccLeft $ lteSuccRight $ residSmaller))
  parseTerm _ _ _ = Left "Invalid Term"

export
parse : String -> Either String (size : Nat ** (Context size, Term size))
parse str = do
  tokens <- tokenize str
  ((size ** (_, context, term)), ([] ** _)) <- parseWhole [] tokens (sizeAccessible tokens)
    | _ => Left "Extra tokens at end of term"
  pure (size ** (context, term))
