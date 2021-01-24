module Parser

import Data.Strings
import Data.Vect
import Decidable.Equality
import Data.Nat

import Tokens

%default total

public export
data Ty = TyBool | TyArr Ty Ty

boolNotArr : TyBool = TyArr x y -> Void
boolNotArr Refl impossible

public export
DecEq Ty where
  decEq TyBool TyBool = Yes Refl
  decEq (TyArr w x) (TyArr y z) with (decEq w y)
    decEq (TyArr w x) (TyArr w z) | (Yes Refl) with (decEq x z)
      decEq (TyArr w x) (TyArr w x) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (TyArr w x) (TyArr w z) | (Yes Refl) | (No contra) = No (\Refl => contra Refl)
    decEq (TyArr w x) (TyArr y z) | (No contra) = No (\Refl => contra Refl)
  decEq TyBool (TyArr _ _) = No boolNotArr
  decEq (TyArr _ _) TyBool = No (\eq => (boolNotArr $ sym eq))

public export
data Term : Nat -> Type where
  TmVar : Fin n -> Term n
  TmAbs : (nm : String) -> (ty : Ty )-> (body : Term (S n)) -> Term n
  TmApp : Term n -> Term n -> Term n
  TmTrue : Term n
  TmFalse : Term n
  TmIf : (g : Term n) -> (t : Term n) -> (e : Term n) -> Term n

weakenTerm : Term n -> n `LTE` m -> Term m
weakenTerm (TmVar k) lte = TmVar (weakenLTE k lte)
weakenTerm (TmAbs name ty body) lte = TmAbs name ty (weakenTerm body (LTESucc lte))
weakenTerm (TmApp x y) lte = TmApp (weakenTerm x lte) (weakenTerm y lte)
weakenTerm TmTrue lte = TmTrue
weakenTerm TmFalse lte = TmFalse
weakenTerm (TmIf g t e) lte = TmIf (weakenTerm g lte) (weakenTerm t lte) (weakenTerm e lte)

public export
data Binding = NameBind | VarBind Ty

public export
Context : Nat ->Type
Context n = Vect n (String, Binding)

public export
addBinding : Context n -> (name : String) -> Ty -> Context (S n)
addBinding context name ty = (name, VarBind ty) :: context

public export
getBinding : Context n -> Fin n -> Binding
getBinding context i = snd (index i context)

absPrec : Prec
absPrec = User 0

appLhsPrec : Prec
appLhsPrec = User 1

appRhsPrec : Prec
appRhsPrec = User 2

ifPrec : Prec
ifPrec = User 3


showPrec : Prec -> Context n -> Term n -> String
showPrec _ context (TmVar j) = fst (index j context)
showPrec d context (TmAbs name ty body) = showParens (d > absPrec) ("\\" ++ name ++ ". " ++ showPrec absPrec (addBinding context name ty) body)
showPrec d context (TmApp x y) = showParens (d >= appRhsPrec) (showPrec appLhsPrec context x ++ " " ++ showPrec appRhsPrec context y)
showPrec _ context TmTrue = "true"
showPrec _ context TmFalse = "false"
showPrec d context (TmIf g t e) = showParens (d >= ifPrec) ("if " ++ (showPrec ifPrec context g) ++ " then " ++ (showPrec ifPrec context t) ++ " else " ++ (showPrec ifPrec context e)) 

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
findInContextOrAdd name context = case findIndex ((== name) . fst) context of
                                       Nothing => Left $ rewrite plusCommutative 1 n in (context ++ [(name, NameBind)])
                                       (Just ind) => Right ind

ParseResult : Nat -> List Token -> Type
ParseResult n tokens = ((size : Nat ** (n `LTE` size, Context size, Term size)), SubList tokens)

findRParen : {0 tokens : List Token} -> SubList tokens -> Either String (SubList tokens)
findRParen (SubLess subList) = SubLess <$> findRParen subList
findRParen (SubTail (TRParen :: xs)) = pure $ SubLess $ SubTail xs
findRParen (SubTail _) = Left "Missing right parenthesis"

mutual
  parseRecur : {n : Nat} -> Context n -> Term n -> (tokens : List Token) -> SubList tokens -> ParseResult n tokens
  parseRecur context term (_ :: tail) (SubLess subList) = let (result, subList') = (parseRecur context term tail subList) in
                                                              (result, SubLess subList')
  parseRecur context term (_ :: tail) (SubTail tail) with (parseTerm context tail)
    parseRecur context term (_ :: tail) (SubTail tail) | (Left _) = ((_ ** (lteRefl, context, term)) , SubTail tail)
    parseRecur context term (_ :: tail) (SubTail tail) | (Right ((size ** (lte, context', term2)), subList')) = let newAppl = TmApp (weakenTerm term lte) term2
                                                                                                                    ((size' ** (lte', contextTerm)), subList'') = parseRecur context' newAppl tail subList' in
                                                                                                                    ((size' ** (lteTransitive lte lte', contextTerm)), SubLess subList'')

  parseWhole : {n : Nat} -> Context n -> (tokens : List Token) -> Either String (ParseResult n tokens)
  parseWhole context tokens = do ((size ** (lte, context', term)), subList) <- parseTerm context tokens
                                 let ((size' ** (lte', contextTerm)), subList') = parseRecur context' term tokens subList
                                 pure ((size' ** (lteTransitive lte lte', contextTerm)), subList')

  parseType : (tokens : List Token) -> Either String (Ty, SubList tokens)
  parseType (TBool :: TArrow :: xs) = do (rhs, subList) <- parseType xs
                                         pure (TyArr TyBool rhs, SubLess $ SubLess $ subList)
  --parseType (TBool :: TArrow :: xs) = subLessHelp $ subLessHelp $ parseMap (TyArr TyBool) $ parseType xs
  parseType (TBool :: xs) = Right $ (TyBool, SubTail xs)
  parseType (TLParen :: xs) = do (type, subList) <- parseType xs
                                 subList' <- findRParen subList
                                 pure (type, SubLess subList')
  parseType _ = Left "Invalid type"

  parseTerm : {n : Nat} -> Context n -> (tokens : List Token) -> Either String (ParseResult n tokens)
  parseTerm context ((TVar name) :: xs) = case findInContextOrAdd name context of
                                               (Left newContext) => Right ((S n ** (lteSuccRight lteRefl, newContext, TmVar last)), SubTail xs)
                                               (Right index) => Right ((n ** (lteRefl, context, TmVar index)), SubTail xs)
  parseTerm context (TLambda :: (TVar name) :: TColon :: xs) = do (type, subList) <- parseType xs
                                                                  (bodyData, subList') <- getBody (addBinding context name type) subList
                                                                  pure (makeApp name type bodyData, SubLess $ SubLess $ SubLess $ subList')
                                                                  where
                                                                    getBody : {m : Nat} -> {tok : List Token} -> Context m -> SubList tok -> Either String (ParseResult m tok)
                                                                    getBody context (SubLess sub) = subLessHelp (getBody context sub)
                                                                    getBody context (SubTail (TDot :: body)) = subLessHelp $ subLessHelp $ parseWhole context body
                                                                    getBody context (SubTail _) = Left "Expected '.'"

                                                                    lteSuccZeroImpossible : LTE (S n) 0 -> Void
                                                                    lteSuccZeroImpossible LTEZero impossible
                                                                    lteSuccZeroImpossible (LTESucc x) impossible

                                                                    makeApp : String -> Ty -> (size : Nat ** (LTE (S n) size, (Context size, Term size))) -> (size : Nat ** (LTE n size, (Context size, Term size)))
                                                                    makeApp name type (0 ** (lte, _)) = void (lteSuccZeroImpossible lte)
                                                                    makeApp name type ((S k) ** (LTESucc lte, (_ :: context), body)) = (k ** (lte, context, TmAbs name type body))
  parseTerm context (TTrue :: xs) = Right ((n ** (lteRefl, context, TmTrue)), SubTail xs)
  parseTerm context (TFalse :: xs) = Right ((n ** (lteRefl, context, TmFalse)), SubTail xs)
  parseTerm context (TIf :: xs) = do ((size ** (lte, context', guardTerm)), subList) <- parseWhole context xs
                                     ((size' ** (lte', context'', thenTerm)), subList') <- getThen context' subList
                                     ((size'' ** (lte'', context''', elseTerm)), subList'') <- getElse context'' subList'
                                     pure ((size'' ** ((lteTransitive lte (lteTransitive lte' lte'')), context''', TmIf (weakenTerm guardTerm (lteTransitive lte' lte'')) (weakenTerm thenTerm lte'') elseTerm)), SubLess subList'')
                                     where
                                       getThen : {m : Nat} -> {tok : List Token} -> Context m -> SubList tok -> Either String (ParseResult m tok)
                                       getThen context (SubLess sub) = subLessHelp $ getThen context sub
                                       getThen context (SubTail (TThen :: ys)) = subLessHelp $ subLessHelp $ parseWhole context ys
                                       getThen context (SubTail _) = Left "Exptected 'then'"

                                       getElse : {m : Nat} -> {tok : List Token} -> Context m -> SubList tok -> Either String (ParseResult m tok)
                                       getElse context (SubLess sub) = subLessHelp $ getElse context sub
                                       getElse context (SubTail (TElse :: ys)) = subLessHelp $ subLessHelp $ parseWhole context ys
                                       getElse context (SubTail _) = Left "Expected 'else'"
  parseTerm context (TLParen :: xs) = do (termData, subList) <- parseWhole context xs
                                         subList' <- findRParen subList
                                         Right (termData, SubLess subList')
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
