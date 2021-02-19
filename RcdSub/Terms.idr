module Terms

import Data.So
import Data.List
import Data.Fin
import Data.Vect
import Decidable.Equality

%default total

Smaller : Char -> Char -> Type
Smaller x y = So (x < y)

smallerAndLargerAbsurd : {0 a, b : Char} -> a `Smaller` b -> b `Smaller`a -> Void
smallerAndLargerAbsurd x y = believe_me ()

soUnique : {0 a : Bool} -> (x, y : So a) -> x = y
soUnique Oh Oh = Refl

smallerToNotEqual : {0 a, b : Char} -> a `Smaller` b -> Not (a = b)
smallerToNotEqual x prf = believe_me ()

decSo : (x : Bool) -> Dec (So x)
decSo True = Yes Oh
decSo False = No uninhabited

decSmaller : (x, y : Char) -> Dec (Smaller x y)
decSmaller x y = decSo (x < y)

notSmallerNotEqIsLarger : {x, y : Char} -> Not (x = y) -> Not (x `Smaller` y) -> y `Smaller` x
notSmallerNotEqIsLarger notEq notSmaller = believe_me Oh

namespace CharList
  public export
  data SortsBefore : List Char -> List Char -> Type where
    EmptyBeforeNonEmpty : SortsBefore [] (x :: xs)
    SmallerCharSortsBefore : x `Smaller` y -> SortsBefore (x :: xs) (y :: ys)
    PrefixSortsBefore : SortsBefore xs ys -> SortsBefore (x :: xs) (x :: ys)

  export
  beforeAndAfterAbsurd : {0 a, b : List Char} -> SortsBefore a b -> SortsBefore b a -> Void
  beforeAndAfterAbsurd EmptyBeforeNonEmpty EmptyBeforeNonEmpty impossible
  beforeAndAfterAbsurd EmptyBeforeNonEmpty (SmallerCharSortsBefore x) impossible
  beforeAndAfterAbsurd EmptyBeforeNonEmpty (PrefixSortsBefore x) impossible
  beforeAndAfterAbsurd (SmallerCharSortsBefore x) (SmallerCharSortsBefore y) = smallerAndLargerAbsurd x y
  beforeAndAfterAbsurd (SmallerCharSortsBefore x) (PrefixSortsBefore y) = smallerToNotEqual x Refl
  beforeAndAfterAbsurd (PrefixSortsBefore x) (SmallerCharSortsBefore y) = smallerToNotEqual y Refl
  beforeAndAfterAbsurd (PrefixSortsBefore x) (PrefixSortsBefore y) = beforeAndAfterAbsurd x y

  export
  sortsBeforeUnique : {0 a, b : List Char} -> (x, y : SortsBefore a b) -> x = y
  sortsBeforeUnique EmptyBeforeNonEmpty EmptyBeforeNonEmpty = Refl
  sortsBeforeUnique (SmallerCharSortsBefore x) (SmallerCharSortsBefore y) = cong SmallerCharSortsBefore (soUnique x y)
  sortsBeforeUnique (SmallerCharSortsBefore x) (PrefixSortsBefore y) = void $ smallerToNotEqual x Refl
  sortsBeforeUnique (PrefixSortsBefore x) (SmallerCharSortsBefore y) = void $ smallerToNotEqual y Refl
  sortsBeforeUnique (PrefixSortsBefore x) (PrefixSortsBefore y) = cong PrefixSortsBefore $ sortsBeforeUnique x y

  export
  sortsBeforeToNotEqual : {0 a, b : List Char} -> SortsBefore a b -> Not (a = b)
  sortsBeforeToNotEqual EmptyBeforeNonEmpty prf = uninhabited prf
  sortsBeforeToNotEqual (SmallerCharSortsBefore charSmaller) Refl = smallerToNotEqual charSmaller Refl
  sortsBeforeToNotEqual (PrefixSortsBefore subABeforeSubB) Refl = sortsBeforeToNotEqual subABeforeSubB Refl

  Uninhabited (SortsBefore x []) where
    uninhabited EmptyBeforeNonEmpty impossible
    uninhabited (SmallerCharSortsBefore x) impossible
    uninhabited (PrefixSortsBefore x) impossible

  prefixNotBeforeNotBefore : (notSortsBefore : SortsBefore xs ys -> Void) -> SortsBefore (x :: xs) (x :: ys) -> Void
  prefixNotBeforeNotBefore _ (SmallerCharSortsBefore smaller) = smallerToNotEqual smaller Refl
  prefixNotBeforeNotBefore notSortsBefore (PrefixSortsBefore smaller) = notSortsBefore smaller

  notSmallerNotPrefixNotBefore : {0 x, y : Char} -> (notSmaller : x `Smaller` y -> Void) -> (notEq : x = y -> Void) -> SortsBefore (x :: xs) (y :: ys) -> Void
  notSmallerNotPrefixNotBefore notSmaller notEq (SmallerCharSortsBefore smaller) = notSmaller smaller
  notSmallerNotPrefixNotBefore notSmaller notEq (PrefixSortsBefore _) = notEq Refl

  export
  decSortsBefore : (x, y : List Char) -> Dec (SortsBefore x y)
  decSortsBefore [] (x :: xs) = Yes EmptyBeforeNonEmpty
  decSortsBefore x [] = No uninhabited
  decSortsBefore (x :: xs) (y :: ys) with (decSmaller x y)
    decSortsBefore (x :: xs) (y :: ys) | (Yes prf) = Yes (SmallerCharSortsBefore prf)
    decSortsBefore (x :: xs) (y :: ys) | (No notSmaller) with (decEq x y)
      decSortsBefore (x :: xs) (x :: ys) | (No notSmaller) | (Yes Refl) with (decSortsBefore xs ys)
        decSortsBefore (x :: xs) (x :: ys) | (No notSmaller) | (Yes Refl) | (Yes prf) = Yes (PrefixSortsBefore prf)
        decSortsBefore (x :: xs) (x :: ys) | (No notSmaller) | (Yes Refl) | (No notSortsBefore) = No (prefixNotBeforeNotBefore notSortsBefore)
      decSortsBefore (x :: xs) (y :: ys) | (No notSmaller) | (No notEq) = No (notSmallerNotPrefixNotBefore notSmaller notEq)

  export
  notBeforeNotEqToAfter : (x, y : List Char) -> Not (x = y) -> Not (SortsBefore x y) -> SortsBefore y x
  notBeforeNotEqToAfter [] [] notEq notBefore = void $ notEq Refl
  notBeforeNotEqToAfter [] (x :: xs) notEq notBefore = void $ notBefore EmptyBeforeNonEmpty
  notBeforeNotEqToAfter (x :: xs) [] notEq notBefore = EmptyBeforeNonEmpty
  notBeforeNotEqToAfter (x :: xs) (y :: ys) notEq notBefore with (decSmaller y x)
    notBeforeNotEqToAfter (x :: xs) (y :: ys) notEq notBefore | (Yes prf) = SmallerCharSortsBefore prf
    notBeforeNotEqToAfter (x :: xs) (y :: ys) notEq notBefore | (No notSmaller) with (decEq y x)
      notBeforeNotEqToAfter (x :: xs) (x :: ys) notEq notBefore | (No notSmaller) | (Yes Refl) = PrefixSortsBefore $ notBeforeNotEqToAfter xs ys (\Refl => notEq Refl) (\isBefore => notBefore $ PrefixSortsBefore isBefore)
      notBeforeNotEqToAfter (x :: xs) (y :: ys) notEq notBefore | (No notSmaller) | (No prefixNotEq) = void $ notBefore $ SmallerCharSortsBefore (notSmallerNotEqIsLarger prefixNotEq notSmaller)

SortsBefore : String -> String -> Type
SortsBefore x y = SortsBefore (unpack x) (unpack y)

sortsBeforeToNotEqual : {0 a, b : String} -> SortsBefore a b -> Not (a = b)
sortsBeforeToNotEqual x prf = sortsBeforeToNotEqual x (cong unpack prf)

decSortsBefore : (x, y : String) -> Dec (SortsBefore x y)
decSortsBefore x y = decSortsBefore (unpack x) (unpack y)

unpackInjective : unpack x = unpack y -> x = y
unpackInjective prf = believe_me (Refl {x=x})

notBeforeNotEqToAfter : (x, y : String) -> Not (x = y) -> Not (SortsBefore x y) -> SortsBefore y x
notBeforeNotEqToAfter x y notEq notBefore = CharList.notBeforeNotEqToAfter (unpack x) (unpack y) (notEq . unpackInjective) notBefore

export
NEQ : String -> String -> Type
NEQ x y = Either (SortsBefore x y) (SortsBefore y x)

neqUnique : {0 a, b : String} -> (x, y : NEQ a b) -> x = y
neqUnique (Left x) (Left y) = cong Left $ sortsBeforeUnique x y
neqUnique (Left x) (Right y) = void $ beforeAndAfterAbsurd x y
neqUnique (Right x) (Left y) = void $ beforeAndAfterAbsurd x y
neqUnique (Right x) (Right y) = cong Right $ sortsBeforeUnique x y

export
neqToNotEqual : NEQ a b -> Not (a = b)
neqToNotEqual (Left aBeforeB) prf = sortsBeforeToNotEqual aBeforeB prf
neqToNotEqual (Right bBeforeA) prf = sortsBeforeToNotEqual bBeforeA (sym prf)

notLeftNotRightNotEither : (notLeft : a -> Void) -> (notRight : b -> Void) -> (Either a b -> Void)
notLeftNotRightNotEither notLeft _ (Left x) = notLeft x
notLeftNotRightNotEither _ notRight (Right x) = notRight x

decNeq : (x, y : String) -> Dec (NEQ x y)
decNeq x y with (decSortsBefore x y)
  decNeq x y | (Yes prf) = Yes (Left prf)
  decNeq x y | (No notLeft) with (decSortsBefore y x)
    decNeq x y | (No notLeft) | (Yes prf) = Yes (Right prf)
    decNeq x y | (No notLeft) | (No notRight) = No (notLeftNotRightNotEither notLeft notRight)

eitherNeqEq: (x, y : String) -> Either (NEQ x y) (x = y)
eitherNeqEq x y with (decEq x y)
  eitherNeqEq x y | (Yes prf) = Right prf
  eitherNeqEq x y | (No contra) with (decSortsBefore x y)
    eitherNeqEq x y | (No _) | (Yes prf) = Left (Left prf)
    eitherNeqEq x y | (No contraEq) | (No contraBefore) = Left (Right (notBeforeNotEqToAfter x y contraEq contraBefore))

export
symNeq : NEQ a b -> NEQ b a
symNeq (Left x) = Right x
symNeq (Right x) = Left x

mutual
  public export
  data BindingKeys : Type where
    EmptySet : BindingKeys
    AddElement : (newVal : String) -> (set : BindingKeys) -> (valIsNew : SetMissing newVal set) -> BindingKeys

  public export
  data SetMissing : String -> BindingKeys -> Type where
    EmptyMissing : SetMissing val EmptySet
    ConsMissing : (elem : String) -> (head : String) -> {tail : BindingKeys} -> (elemNotHead : elem `NEQ` head) -> (elemNotInTail : SetMissing elem tail) -> {existingSetMissing : SetMissing head tail} -> SetMissing elem (AddElement head tail existingSetMissing)

public export
length : BindingKeys -> Nat
length EmptySet = 0
length (AddElement _ set _) = S (length set)

emptyNotAdd : {0 x : String} -> {0 y : BindingKeys} -> {0 z : SetMissing x y} -> EmptySet = AddElement x y z -> Void
emptyNotAdd Refl impossible

public export
data InBounds : (k : Nat) -> (set : BindingKeys) -> Type where
  InFirst : InBounds Z (AddElement head set headIsNew)
  InLater : InBounds k set -> InBounds (S k) (AddElement head set headIsNew)

public export
Uninhabited (InBounds i EmptySet) where
  uninhabited InFirst impossible
  uninhabited (InLater x) impossible

public export
index : (n : Nat) -> (set : BindingKeys) -> {auto 0 ok : InBounds n set} -> String
index 0 (AddElement head _ _) {ok = InFirst} = head
index (S k) (AddElement head set headIsNew) {ok = (InLater ok)} = index k set

export
getIndex : (name : String) -> (set : BindingKeys) -> Either (SetMissing name set) (n : Nat ** inBounds : InBounds n set ** name = index n set)
getIndex name EmptySet = Left EmptyMissing
getIndex name (AddElement head tail _) = case eitherNeqEq name head of
                                              (Right eqPrf) => Right (Z ** InFirst ** eqPrf)
                                              (Left neq) => case getIndex name tail of
                                                                 (Left tailMissing) => Left (ConsMissing name head neq tailMissing)
                                                                 (Right (n ** inBounds ** isIndex)) => Right (S n ** InLater inBounds ** isIndex)

export
succInbounds : InBounds i names -> InBounds (S i) (AddElement name names nameNotInNames)
succInbounds InFirst = InLater InFirst
succInbounds (InLater x) = InLater (succInbounds x)

export
succIndexOfAddElementEq : (i : Nat) -> {0 ok : InBounds i names} -> index i {ok} names = index (S i) {ok=succInbounds {nameNotInNames} ok} (AddElement name names nameNotInNames)
succIndexOfAddElementEq 0 {ok = InFirst} = Refl
succIndexOfAddElementEq (S i) {ok = (InLater ok)} = succIndexOfAddElementEq i

export
index0OfAddElementNew : index 0 (AddElement new set isNew) = new
index0OfAddElementNew = Refl

export
setMissingIndexAbsurd : (set : BindingKeys) -> (i : Nat) -> {0 ok : InBounds i set} -> SetMissing (index i set {ok}) set -> Void
setMissingIndexAbsurd (AddElement head tail headIsNew) 0 (ConsMissing _ head elemNotInHead elemNotInTail) {ok=InFirst} = neqToNotEqual elemNotInHead Refl
setMissingIndexAbsurd (AddElement head tail headIsNew) (S i) (ConsMissing _ head elemNotInHead elemNotInTail) {ok=InLater ok} = setMissingIndexAbsurd tail i elemNotInTail

inBoundsUnique : (set : BindingKeys) -> (i : Nat) -> {0 ok,ok' : InBounds i set} -> ok = ok'
inBoundsUnique EmptySet i {ok} = void $ uninhabited ok
inBoundsUnique (AddElement newVal set valIsNew) 0 {ok=InFirst} {ok'=InFirst} = Refl
inBoundsUnique (AddElement newVal set valIsNew) (S k) {ok=InLater ok} {ok'=InLater ok'} = cong InLater (inBoundsUnique set k)

public export
inBoundsToFinLength: (n : Nat) -> {0 set : BindingKeys} -> {auto 0 ok : InBounds n set} -> Fin (length set)
inBoundsToFinLength 0 {ok = InFirst} = FZ
inBoundsToFinLength (S k) {ok = (InLater ok)} = FS (inBoundsToFinLength k)

valIsNewIsUnique : (valIsNewA, valIsNewB : SetMissing newVal set) -> valIsNewA = valIsNewB
valIsNewIsUnique EmptyMissing EmptyMissing = Refl
valIsNewIsUnique (ConsMissing newVal head newNotHeadA newNotInTailA) (ConsMissing newVal head newNotHeadB newNotInTailB) = rewrite the (newNotHeadA = newNotHeadB) (neqUnique newNotHeadA newNotHeadB) in rewrite valIsNewIsUnique newNotInTailA newNotInTailB in Refl

export
indexSameToInBoundsSame : (set : BindingKeys) -> (i, j : Nat) -> {0 ok : InBounds i set} -> {0 ok' : InBounds j set} -> index i {ok} set = index j {ok=ok'} set -> (inBoundsToFinLength i {ok}) = (inBoundsToFinLength j {ok=ok'})
indexSameToInBoundsSame (AddElement newVal set valIsNew) 0 0 prf = rewrite inBoundsUnique (AddElement newVal set valIsNew) 0 {ok} {ok'} in Refl
indexSameToInBoundsSame (AddElement newVal set valIsNew) 0 (S k) {ok = InFirst} {ok' = InLater ok'} prf = void $ setMissingIndexAbsurd set k (replace prf valIsNew {p = (\x=>SetMissing x set)})
indexSameToInBoundsSame (AddElement newVal set valIsNew) (S k) 0 {ok = InLater ok} {ok' = InFirst} prf = void $ setMissingIndexAbsurd set k (replace (sym prf) valIsNew {p = (\x=>SetMissing x set)})
indexSameToInBoundsSame (AddElement newVal set valIsNew) (S k) (S j) {ok = InLater ok} {ok' = InLater ok'} prf = cong FS (indexSameToInBoundsSame set k j prf)

export
setMissingToIndexNeq : {name : String} -> {names : BindingKeys} -> (nameIsNew : SetMissing name names) -> (i : Nat) -> {0 ok : InBounds i names} -> NEQ name (index i names)
setMissingToIndexNeq (ConsMissing name head elemNotHead _) 0 {ok=InFirst} = elemNotHead
setMissingToIndexNeq (ConsMissing name _ _ elemNotInTail) (S i) {ok=InLater ok} = setMissingToIndexNeq elemNotInTail i

DecEq BindingKeys where
  decEq EmptySet EmptySet = Yes Refl
  decEq EmptySet (AddElement newVal set valIsNew) = No emptyNotAdd
  decEq (AddElement newVal set valIsNew) EmptySet = No (\eq => emptyNotAdd $ sym eq)
  decEq (AddElement newValA setA valIsNewA) (AddElement newValB setB valIsNewB) with (decEq newValA newValB)
    decEq (AddElement newValA setA valIsNewA) (AddElement newValB setB valIsNewB) | (No contra) = No (\Refl => contra Refl)
    decEq (AddElement newVal setA valIsNewA) (AddElement newVal setB valIsNewB) | (Yes Refl) with (decEq setA setB)
      decEq (AddElement newVal setA valIsNewA) (AddElement newVal setB valIsNewB) | (Yes Refl) | (No contra) = No (\Refl => contra Refl)
      decEq (AddElement newVal set valIsNewA) (AddElement newVal set valIsNewB) | (Yes Refl) | (Yes Refl) = Yes (rewrite valIsNewIsUnique valIsNewA valIsNewB in Refl)

export
decSetMissing : (elem : String) -> (set : BindingKeys) -> Dec (SetMissing elem set)
decSetMissing elem EmptySet = Yes EmptyMissing
decSetMissing elem (AddElement newVal set valIsNew) with (decNeq elem newVal)
  decSetMissing elem (AddElement newVal set valIsNew) | (Yes neqHead) with (decSetMissing elem set)
    decSetMissing elem (AddElement newVal set valIsNew) | (Yes neqHead) | (Yes notInTail) = Yes (ConsMissing elem newVal neqHead notInTail)
    decSetMissing elem (AddElement newVal set valIsNew) | (Yes neqHead) | (No contra) = No (\(ConsMissing _ _ _ notInTail) => contra notInTail)
  decSetMissing elem (AddElement newVal set valIsNew) | (No contra) = No (\(ConsMissing _ _ neqHead _) => contra neqHead)

export
succIndexOfConsEq : (i : Nat) -> {0 ok : InBounds i names} -> {0 typesA : Vect (length names) v} -> {0 name : String} -> {0 nameNotInNames : SetMissing name names} -> index (inBoundsToFinLength i {ok}) typesA = index (inBoundsToFinLength (S i) {ok=succInbounds {nameNotInNames} ok}) (tyA :: typesA)
succIndexOfConsEq 0 {ok = InFirst} = Refl
succIndexOfConsEq (S i) {ok = (InLater ok)} {typesA = (tyA :: typesA)} = succIndexOfConsEq i

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
