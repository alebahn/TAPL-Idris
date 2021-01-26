module Parser

import Data.Strings
import Data.Vect
import Decidable.Equality
import Data.Nat
import Control.WellFounded
import Data.List1

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
  parseRepeat : {n : Nat} -> (context : Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String ((size : Nat ** (n `LTE` size, Context size, List1 (Term size))), (resid : List Token ** resid `Smaller` tokens))
  parseRepeat context tokens (Access acc) = do ((n' ** (lte, context', term)), (resid ** residSmaller)) <- parseTerm context tokens (Access acc)
                                               pure $ case parseRepeat context' resid (acc resid residSmaller)  of
                                                           (Left _) => ((n' ** (lte, context', term ::: [])), (resid ** residSmaller))
                                                           (Right ((n'' ** (lte', context'', terms)), (resid' ** residSmaller'))) => ((n'' ** (lteTransitive lte lte', context'', liftTerm term lte' ::: forget terms)), (resid' ** (lteTransitive (lteSuccRight residSmaller') residSmaller)))

  parseWhole : {n : Nat} -> (context: Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (ParseResult n tokens)
  parseWhole context tokens acc = do ((n ** (lte, context', terms)), resid) <- parseRepeat context tokens acc
                                     pure $ ((n ** (lte, context', (foldl1 id TmApp terms))), resid)

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
