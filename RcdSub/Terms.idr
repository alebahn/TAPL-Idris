module Terms

import Data.List
import Data.Fin
import Data.Vect
import Decidable.Equality

import BindingKeys

%default total

public export
record RecordMap (v : Type) where
  constructor MkRecordMap
  keys : BindingKeys
  values : Vect (length keys) v

DecEq v => DecEq (RecordMap v) where
  decEq (MkRecordMap keysA valuesA) (MkRecordMap keysB valuesB) with (decEq keysA keysB)
    decEq (MkRecordMap keysA valuesA) (MkRecordMap keysB valuesB) | (No contra) = No (\Refl => contra Refl)
    decEq (MkRecordMap keys valuesA) (MkRecordMap keys valuesB) | (Yes Refl) with (decEq valuesA valuesB)
      decEq (MkRecordMap keys values) (MkRecordMap keys values) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (MkRecordMap keys valuesA) (MkRecordMap keys valuesB) | (Yes Refl) | (No contra) = No (\Refl => contra Refl)

public export
Functor RecordMap where
  map f (MkRecordMap keys values) = MkRecordMap keys (f <$> values)

public export
data Ty = TyRec (RecordMap Ty) | TyArr Ty Ty | TyTop | TyBot | TyBool

mutual
  public export
  data Term : Nat -> Type where
    TmVar : Fin n -> Term n
    TmAbs : (nm : String) -> (ty : Ty )-> (body : Term (S n)) -> Term n
    TmApp : Term n -> Term n -> Term n
    TmRec : RecordMap (Term n) -> Term n
    TmProj : Term n -> (name : String) -> Term n
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

projPrec : Prec
projPrec = User 1

appLhsPrec : Prec
appLhsPrec = User 2

appRhsPrec : Prec
appRhsPrec = User 3

ifPrec : Prec
ifPrec = User 4

joinWith : String -> List String -> String
joinWith glue [] = ""
joinWith glue (x :: xs) = foldl (++) x ((glue ++) <$> xs)

mutual
  showRecord : Context n -> RecordMap (Term n) -> List String
  showRecord context (MkRecordMap keys values) = showRecord' context keys values
    where
      showRecord' : Context n -> (keys : BindingKeys) -> (values : Vect (length keys) (Term n)) -> List String
      showRecord' context EmptySet [] = []
      showRecord' context (AddElement newVal set _) (val :: vals) = (newVal ++ " = " ++ showPrec Open context val) :: showRecord' context set vals

  showPrec : Prec -> Context n -> Term n -> String
  showPrec _ context (TmVar j) = fst (index j context)
  showPrec d context (TmAbs name ty body) = showParens (d > absPrec) ("\\" ++ name ++ ". " ++ showPrec absPrec (addBinding context name ty) body)
  showPrec d context (TmApp x y) = showParens (d >= appRhsPrec) (showPrec appLhsPrec context x ++ " " ++ showPrec appRhsPrec context y)
  showPrec _ context (TmRec recordMap) = "{" ++ joinWith ", " (showRecord context recordMap) ++ "}"
  showPrec d context (TmProj x y) = showParens (d > projPrec) (showPrec projPrec context x ++ "." ++ y)
  showPrec _ context TmTrue = "true"
  showPrec _ context TmFalse = "false"
  showPrec d context (TmIf g t e) = showParens (d >= ifPrec) ("if " ++ (showPrec ifPrec context g) ++ " then " ++ (showPrec ifPrec context t) ++ " else " ++ (showPrec ifPrec context e)) 

export
show : Context n -> Term n -> String
show context term = showPrec Open context term
