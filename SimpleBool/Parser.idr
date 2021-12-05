module Parser

import Data.String
import Data.Vect
import Decidable.Equality
import Data.Nat
import Control.WellFounded
import Data.List1
import Data.DPair

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

public export
Context : Nat ->Type
Context n = Vect n (String, Ty)

public export
addBinding : Context n -> (name : String) -> Ty -> Context (S n)
addBinding context name ty = (name, ty) :: context

public export
getBindingType : Context n -> Fin n -> Ty
getBindingType context i = snd (index i context)

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

mutual
  parsePartType : (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (Ty, (Subset (List Token) (\resid => resid `Smaller` tokens)))
  parsePartType (TBool :: xs) _ = Right (TyBool, (Element xs (reflexive {rel = LTE})))
  parsePartType (TLParen :: xs) (Access acc) = do (ty, (Element (TRParen :: resid) residSmaller)) <- parseType xs (acc xs (reflexive {rel = LTE}))
                                                    | _ => Left "Expected ')'"
                                                  pure (ty, (Element resid (lteSuccLeft $ lteSuccRight residSmaller)))
  parsePartType _ _ = Left "Invalid type"

  parseType : (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (Ty, (Subset (List Token) (\resid => resid `Smaller` tokens)))
  parseType tokens (Access acc) = do (ty, (Element resid residSmaller)) <- parsePartType tokens (Access acc)
                                     case resid of
                                          (TArrow :: xs) => do (tyRight, (Element resid' residSmaller')) <- parseType xs (acc xs (lteSuccLeft residSmaller))
                                                               pure (TyArr ty tyRight, (Element resid' (transitive {rel=LTE} residSmaller' (lteSuccLeft $ lteSuccLeft residSmaller))))
                                          xs => Right (ty, (Element xs residSmaller))

ParseResult : Nat -> List Token -> Type
ParseResult n tokens = (Term n, (Subset (List Token) (\resid => resid `Smaller` tokens)))

mutual
  parseTerms : {n : Nat} -> (context : Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (List1 (Term n), (Subset (List Token) (\resid => resid `Smaller` tokens)))
  parseTerms context tokens (Access acc) = do (term, (Element resid residSmaller)) <- parseTerm context tokens (Access acc)
                                              case parseTerms context resid (acc resid residSmaller) of
                                                   (Left _) => Right (term ::: [], (Element resid residSmaller))
                                                   (Right (terms, (Element resid' residSmaller'))) => Right (term ::: (forget terms), (Element resid' (transitive {rel=LTE} residSmaller' (lteSuccLeft residSmaller))))

  parseWhole : {n : Nat} -> (context : Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (ParseResult n tokens)
  parseWhole context tokens acc = do (terms, resid) <- parseTerms context tokens acc
                                     Right (foldl1 TmApp terms, resid)

  parseTerm : {n : Nat} -> (context : Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (ParseResult n tokens)
  parseTerm context ((TVar name) :: xs) (Access acc) = case findIndex ((== name) . fst) context of
                                                            Nothing => Left (name ++ " is not bound")
                                                            (Just idx) => Right (TmVar idx, (Element xs (reflexive {rel = LTE})))
  parseTerm context (TLambda :: (TVar name) :: TColon :: xs) (Access acc) = do (type, (Element (TDot :: ys) residSmaller)) <- parseType xs (acc xs (lteSuccRight $ lteSuccRight $ (reflexive {rel = LTE})))
                                                                                | _ => Left "Expected '.'"
                                                                               (body, (Element resid residSmaller')) <- parseWhole (addBinding context name type) ys (acc ys (lteSuccLeft $ lteSuccRight $ lteSuccRight $ lteSuccRight residSmaller))
                                                                               pure (TmAbs name type body, (Element resid (transitive {rel=LTE} residSmaller' (lteSuccLeft $ lteSuccLeft $ lteSuccRight $ lteSuccRight $ lteSuccRight residSmaller))))
  parseTerm context (TTrue :: xs) (Access acc) = Right (TmTrue, (Element xs (reflexive {rel = LTE})))
  parseTerm context (TFalse :: xs) (Access acc) = Right (TmFalse, (Element xs (reflexive {rel = LTE})))
  parseTerm context (TIf :: xs) (Access acc) = do (gTerm, (Element (TThen :: gResid) gSmaller)) <- parseWhole context xs (acc xs (reflexive {rel = LTE}))
                                                    | _ => Left "Expected then"
                                                  (tTerm, (Element (TElse :: tResid) tSmaller)) <- parseWhole context gResid (acc gResid (lteSuccLeft $ lteSuccRight gSmaller))
                                                    | _ => Left "Expected else"
                                                  (eTerm, (Element eResid eSmaller)) <- parseWhole context tResid (acc tResid (transitive {rel=LTE} (lteSuccLeft $ lteSuccRight tSmaller) (lteSuccLeft $ lteSuccRight gSmaller)))
                                                  pure (TmIf gTerm tTerm eTerm, (Element eResid (transitive {rel=LTE} (lteSuccRight eSmaller) (transitive {rel=LTE} (lteSuccLeft $ lteSuccRight tSmaller) (lteSuccLeft $ lteSuccRight gSmaller)))))
  parseTerm context (TLParen :: xs) (Access acc) = do (term, (Element (TRParen :: resid) residSmaller)) <- parseWhole context xs (acc xs (reflexive {rel = LTE}))
                                                       | _ => Left "Expected ')'"
                                                      Right (term, (Element resid (lteSuccLeft $ lteSuccRight residSmaller)))
  parseTerm _ _ _ = Left "Invalid Term"

export
parse : String -> Either String (Term 0)
parse str = do
  tokens <- tokenize str
  (term, (Element [] _)) <- parseWhole [] tokens (sizeAccessible tokens)
    | _ => Left "Extra tokens at end of term"
  pure term
