module Term

import Data.Fin

import Ty

%default total

public export
data Term : Nat -> Nat -> Type where
  TmVar : Fin n -> Term n m
  TmAbs : (ty : Ty m)-> (body : Term (S n) m) -> Term n m
  TmApp : Term n m -> Term n m -> Term n m
  TmTAbs : (body : Term n (S m)) -> Term n m
  TmTApp : Term n m -> Ty m -> Term n m
  TmPack : Ty m -> Term n m -> Ty m -> Term n m
  TmUnpack : Term n m -> Term (S n) (S m) -> Term n m

{-
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
-}
