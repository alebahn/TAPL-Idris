module Parser

import Data.Strings
import Data.Vect
import Decidable.Equality
import Data.Nat

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

findInContextOrAdd : String -> Context n -> Either (Context (S n)) (Fin n)
findInContextOrAdd name context = case elemIndex name context of
                                       Nothing => Left $ rewrite plusCommutative 1 n in (context ++ [name])
                                       (Just ind) => Right ind

ParseResult : Nat -> List Token -> Type
ParseResult n tokens = ((size : Nat ** (n `LTE` size, Context size, Term size)), SubList tokens)

mutual
  parseRecur : {n : Nat} -> Context n -> Term n -> (tokens : List Token) -> SubList tokens -> ParseResult n tokens
  parseRecur context term (_ :: tail) (SubLess subList) = let (result, subList') = (parseRecur context term tail subList) in
                                                              (result, SubLess subList')
  parseRecur context term (_ :: tail) (SubTail tail) with (parseTerm context tail)
    parseRecur context term (_ :: tail) (SubTail tail) | (Left _) = ((_ ** (lteRefl, context, term)) , SubTail tail)
    parseRecur context term (_ :: tail) (SubTail tail) | (Right ((size ** (lte, context', term2)), subList')) = let newAppl = TmApp (liftTerm term lte) term2
                                                                                                                    ((size' ** (lte', contextTerm)), subList'') = parseRecur context' newAppl tail subList' in
                                                                                                                    ((size' ** (lteTransitive lte lte', contextTerm)), SubLess subList'')

  parseWhole : {n : Nat} -> Context n -> (tokens : List Token) -> Either String (ParseResult n tokens)
  parseWhole context tokens = do ((size ** (lte, context', term)), subList) <- parseTerm context tokens
                                 let ((size' ** (lte', contextTerm)), subList') = parseRecur context' term tokens subList
                                 pure ((size' ** (lteTransitive lte lte', contextTerm)), subList')

  parseTerm : {n : Nat} -> Context n -> (tokens : List Token) -> Either String (ParseResult n tokens)
  parseTerm context ((TVar name) :: xs) = case findInContextOrAdd name context of
                                               (Left newContext) => Right ((S n ** (lteSuccRight lteRefl, newContext, TmVar last)), SubTail xs)
                                               (Right index) => Right ((n ** (lteRefl, context, TmVar index)), SubTail xs)
  parseTerm context (TLambda :: (TVar name) :: TDot :: xs) = do (bodyData, subList) <- parseWhole (name :: context) xs
                                                                pure (makeApp name bodyData, SubLess $ SubLess $ SubLess $ subList)
                                                                where
                                                                  lteSuccZeroImpossible : LTE (S n) 0 -> Void
                                                                  lteSuccZeroImpossible LTEZero impossible
                                                                  lteSuccZeroImpossible (LTESucc x) impossible

                                                                  makeApp : String -> (size : Nat ** (LTE (S n) size, (Vect size String, Term size))) -> (size : Nat ** (LTE n size, (Vect size String, Term size)))
                                                                  makeApp name (0 ** (lte, _)) = void (lteSuccZeroImpossible lte)
                                                                  makeApp name ((S k) ** (LTESucc lte, (_ :: context), body)) = (k ** (lte, context, TmAbs name body))
  parseTerm context (TLParen :: xs) = do (termData, subList) <- parseWhole context xs
                                         subList' <- findRParen subList
                                         Right (termData, SubLess subList')
                                         where
                                           findRParen : {0 tokens : List Token} -> SubList tokens -> Either String (SubList tokens)
                                           findRParen (SubLess subList) = do subList' <- findRParen subList
                                                                             pure $ SubLess subList'
                                           findRParen (SubTail (TRParen :: xs)) = pure $ SubLess $ SubTail xs
                                           findRParen (SubTail _) = Left "Missing right parenthesis"
  parseTerm _ _ = Left "Invalid Term"

isSubListEmpty : SubList list -> Bool
isSubListEmpty (SubLess sub) = isSubListEmpty sub
isSubListEmpty (SubTail []) = True
isSubListEmpty (SubTail _) = False

export
parse : String -> Either String (size : Nat ** (Context size, Term size))
parse str = do
  tokens <- tokenize str
  ((size ** (_, context, term)), remaining) <- parseWhole [] tokens
  if isSubListEmpty remaining
     then pure (size ** (context, term))
     else Left "Extra tokens at end of term"
