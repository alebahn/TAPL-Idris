module BindingKeys

import Data.Fin
import Data.Nat
import Data.List
import Data.So
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
data NEQ : String -> String -> Type where
  NeqBefore : SortsBefore x y -> NEQ x y
  NeqAfter : SortsBefore y x -> NEQ x y
--NEQ x y = Either (SortsBefore x y) (SortsBefore y x)

neqUnique : {0 a, b : String} -> (x, y : NEQ a b) -> x = y
neqUnique (NeqBefore x) (NeqBefore y) = cong NeqBefore $ sortsBeforeUnique x y
neqUnique (NeqBefore x) (NeqAfter y) = void $ beforeAndAfterAbsurd x y
neqUnique (NeqAfter x) (NeqBefore y) = void $ beforeAndAfterAbsurd x y
neqUnique (NeqAfter x) (NeqAfter y) = cong NeqAfter $ sortsBeforeUnique x y

export
neqToNotEqual : NEQ a b -> Not (a = b)
neqToNotEqual (NeqBefore aBeforeB) prf = sortsBeforeToNotEqual aBeforeB prf
neqToNotEqual (NeqAfter bBeforeA) prf = sortsBeforeToNotEqual bBeforeA (sym prf)

notBeforeNotAfterNotEqual : (notBefore : SortsBefore x y -> Void) -> (notAfter : SortsBefore y x -> Void) -> (NEQ x y -> Void)
notBeforeNotAfterNotEqual notBefore _ (NeqBefore x) = notBefore x
notBeforeNotAfterNotEqual _ notAfter (NeqAfter x) = notAfter x

decNeq : (x, y : String) -> Dec (NEQ x y)
decNeq x y with (decSortsBefore x y)
  decNeq x y | (Yes prf) = Yes (NeqBefore prf)
  decNeq x y | (No notBefore) with (decSortsBefore y x)
    decNeq x y | (No notBefore) | (Yes prf) = Yes (NeqAfter prf)
    decNeq x y | (No notBefore) | (No notAfter) = No (notBeforeNotAfterNotEqual notBefore notAfter)

export
eitherNeqEq: (x, y : String) -> Either (NEQ x y) (x = y)
eitherNeqEq x y with (decEq x y)
  eitherNeqEq x y | (Yes prf) = Right prf
  eitherNeqEq x y | (No contra) with (decSortsBefore x y)
    eitherNeqEq x y | (No _) | (Yes prf) = Left (NeqBefore prf)
    eitherNeqEq x y | (No contraEq) | (No contraBefore) = Left (NeqAfter (notBeforeNotEqToAfter x y contraEq contraBefore))

export
%hint
symNeq : NEQ a b -> NEQ b a
symNeq (NeqBefore x) = NeqAfter x
symNeq (NeqAfter x) = NeqBefore x

mutual
  public export
  data BindingKeys : Type where
    EmptySet : BindingKeys
    AddElement : (newVal : String) -> (set : BindingKeys) -> (valIsNew : SetMissing newVal set) -> BindingKeys

  public export
  data SetMissing : String -> BindingKeys -> Type where
    EmptyMissing : SetMissing val EmptySet
    ConsMissing : (0 elem : String) -> (0 head : String) -> {0 tail : BindingKeys} -> (elemNotHead : elem `NEQ` head) -> (elemNotInTail : SetMissing elem tail) -> {existingSetMissing : SetMissing head tail} -> SetMissing elem (AddElement head tail existingSetMissing)

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

public export
IndexData : String -> BindingKeys -> Type
IndexData name set = (n : Nat ** inBounds : InBounds n set ** name = index n set)

public export
GetIndexData : String -> BindingKeys -> Type
GetIndexData name set = Either (SetMissing name set) (IndexData name set)

public export
getIndex : (name : String) -> (set : BindingKeys) -> GetIndexData name set
getIndex name EmptySet = Left EmptyMissing
getIndex name (AddElement head tail _) = case eitherNeqEq name head of
                                              (Right eqPrf) => Right (Z ** InFirst ** eqPrf)
                                              (Left neq) => case getIndex name tail of
                                                                 (Left tailMissing) => Left (ConsMissing name head neq tailMissing)
                                                                 (Right (n ** inBounds ** isIndex)) => Right (S n ** InLater inBounds ** isIndex)

export
missingIndexAbsurd : (keys : BindingKeys) -> {var : String} -> (ind : Nat) -> (inBounds : InBounds ind keys) -> (isInd : var = index ind keys) -> SetMissing var keys -> Void
missingIndexAbsurd (AddElement head set headIsNew) 0 InFirst isInd (ConsMissing var head elemNotHead elemNotInTail) = neqToNotEqual elemNotHead isInd
missingIndexAbsurd (AddElement head set headIsNew) (S k) (InLater inBounds) isInd (ConsMissing var head elemNotHead elemNotInTail) = missingIndexAbsurd set k inBounds isInd elemNotInTail

export
getIndexUniqueRight : (keys : BindingKeys) -> {var : String} -> (ind : Nat) -> (inBounds : InBounds ind keys) -> (isInd : var = index ind keys) -> getIndex var keys = Right (ind ** inBounds ** isInd)
getIndexUniqueRight EmptySet ind inBounds isInd = absurd inBounds
getIndexUniqueRight (AddElement newVal set valIsNew) 0 InFirst isInd with (eitherNeqEq var newVal)
  getIndexUniqueRight (AddElement var set valIsNew) 0 InFirst Refl | (Right Refl) = Refl
  getIndexUniqueRight (AddElement newVal set valIsNew) 0 InFirst isInd | (Left neq) = void $ neqToNotEqual neq isInd
getIndexUniqueRight (AddElement newVal set valIsNew) (S ind) (InLater inBounds) isInd with (eitherNeqEq var newVal)
  getIndexUniqueRight (AddElement var set valIsNew) (S ind) (InLater inBounds) isInd | (Right Refl) = void $ missingIndexAbsurd set ind inBounds isInd valIsNew
  getIndexUniqueRight (AddElement newVal set valIsNew) (S ind) (InLater inBounds) isInd | (Left neq) = rewrite getIndexUniqueRight set ind inBounds isInd in Refl

export
getIndexUniqueLeft : (keys : BindingKeys) -> {var : String} -> (varMissing : SetMissing var keys) -> getIndex var keys = Left varMissing
getIndexUniqueLeft EmptySet EmptyMissing = Refl
getIndexUniqueLeft (AddElement newVal set valIsNew) (ConsMissing var newVal elemNotHead elemNotInTail) with (eitherNeqEq var newVal)
  getIndexUniqueLeft (AddElement newVal set valIsNew) (ConsMissing var newVal elemNotHead elemNotInTail) | (Right eqPrf) = void $ neqToNotEqual elemNotHead eqPrf
  getIndexUniqueLeft (AddElement newVal set valIsNew) (ConsMissing var newVal elemNotHead elemNotInTail) | (Left elemNotHead') = rewrite getIndexUniqueLeft set elemNotInTail in rewrite neqUnique elemNotHead' elemNotHead in Refl

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

export
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
indexInjective : {n, m : Nat} -> {set : BindingKeys} -> {inBoundsN : InBounds n set} -> {inBoundsM : InBounds m set} -> index n set = index m set -> n = m
indexInjective {n = 0} {m = 0} prf = Refl
indexInjective {n = 0} {m = (S k)} {set = (AddElement newVal set valIsNew)} {inBoundsN = InFirst} {inBoundsM = (InLater inBounds)} prf = void $ setMissingIndexAbsurd set k (replace {p = (\x => SetMissing x set)} prf valIsNew)
indexInjective {n = (S k)} {m = 0} {set = (AddElement newVal set valIsNew)} {inBoundsN = (InLater inBounds)}  {inBoundsM = InFirst} prf = void $ setMissingIndexAbsurd set k (replace {p = (\x => SetMissing x set)} (sym prf) valIsNew)
indexInjective {n = (S k)} {m = (S j)} prf {inBoundsN = (InLater inBoundsN)} {inBoundsM = (InLater inBoundsM)} = cong S (indexInjective prf)

export
setMissingToIndexNeq : {name : String} -> {names : BindingKeys} -> (nameIsNew : SetMissing name names) -> (i : Nat) -> {0 ok : InBounds i names} -> NEQ name (index i names)
setMissingToIndexNeq (ConsMissing name head elemNotHead _) 0 {ok=InFirst} = elemNotHead
setMissingToIndexNeq (ConsMissing name _ _ elemNotInTail) (S i) {ok=InLater ok} = setMissingToIndexNeq elemNotInTail i

export
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

mutual
  export
  snoc : (xs : BindingKeys) -> (x : String) -> SetMissing x xs -> BindingKeys
  snoc EmptySet x xMissing = (AddElement x EmptySet xMissing)
  snoc (AddElement newVal set valIsNew) x (ConsMissing x newVal elemNotHead elemNotInTail) = AddElement newVal (snoc set x elemNotInTail) (snocMissing newVal set x valIsNew (symNeq elemNotHead))

  export
  snocMissing : (0 elem : String) -> (init : BindingKeys) -> (0 last : String) -> (elemNotInInit : SetMissing elem init) -> (elemNotlast : elem `NEQ` last) -> {existingSetMissing : SetMissing last init} -> SetMissing elem (snoc init last existingSetMissing)
  snocMissing elem EmptySet last elemNotInInit elemNotlast = ConsMissing elem last elemNotlast elemNotInInit
  snocMissing elem (AddElement newVal set valIsNew) last (ConsMissing elem newVal elemNotHead elemNotInTail) elemNotlast {existingSetMissing = (ConsMissing last newVal lastNotNewVal lastNotInSet)} = ConsMissing elem newVal elemNotHead (snocMissing elem set last elemNotInTail elemNotlast)

snocMissingInv : (0 elem : String) -> (init : BindingKeys) -> (last : String) -> {existingSetMissing : SetMissing last init} -> (snocMissing : SetMissing elem (snoc init last existingSetMissing)) -> (SetMissing elem init)
snocMissingInv elem EmptySet last (ConsMissing elem last elemNotHead elemNotInTail) = elemNotInTail
snocMissingInv elem (AddElement newVal set valIsNew) last {existingSetMissing = (ConsMissing last newVal elemNotHead elemNotInTail)} (ConsMissing elem newVal newValNotElem snocMissing) = ConsMissing elem newVal newValNotElem (snocMissingInv elem set last snocMissing)

snocMissingInvNeq : (0 elem : String) -> (init : BindingKeys) -> (last : String) -> {existingSetMissing : SetMissing last init} -> (snocMissing : SetMissing elem (snoc init last existingSetMissing)) -> NEQ elem last
snocMissingInvNeq elem EmptySet last (ConsMissing elem last elemNotHead elemNotInTail) = elemNotHead
snocMissingInvNeq elem (AddElement newVal set valIsNew) last {existingSetMissing = (ConsMissing last newVal elemNotHead elemNotInTail)} (ConsMissing elem newVal _ snocMissing) = snocMissingInvNeq elem set last snocMissing

export
lengthSnocSucc : (xs : BindingKeys) -> (x : String) -> (missing : SetMissing x xs) -> length (snoc xs x missing) = S (length xs)
lengthSnocSucc EmptySet x missing = Refl
lengthSnocSucc (AddElement newVal set valIsNew) x (ConsMissing x newVal elemNotHead elemNotInTail) = cong S (lengthSnocSucc set x elemNotInTail)

public export
data Disjoint : BindingKeys -> BindingKeys -> Type where
  EmptyDisjoint : Disjoint x EmptySet
  AddDisjoint : SetMissing newVal x -> Disjoint x y -> Disjoint x (AddElement newVal y valIsNew)

export
symDisjoint : {a, b : BindingKeys} -> Disjoint a b -> Disjoint b a
symDisjoint {a = EmptySet} _ = EmptyDisjoint
symDisjoint {a = (AddElement newVal set valIsNew)} EmptyDisjoint = AddDisjoint EmptyMissing (symDisjoint EmptyDisjoint)
symDisjoint {a = (AddElement newVal set valIsNew)} {b = (AddElement newVal' set' valIsNew')} (AddDisjoint (ConsMissing newVal' newVal elemNotHead elemNotInTail) y) =
  let (AddDisjoint c d) = symDisjoint y in
      AddDisjoint (ConsMissing newVal newVal' (symNeq elemNotHead) c) (symDisjoint (AddDisjoint elemNotInTail (symDisjoint d)))

export
disjointUnique : (x, y : Disjoint a b) -> x = y
disjointUnique EmptyDisjoint EmptyDisjoint = Refl
disjointUnique (AddDisjoint x z) (AddDisjoint y w) = rewrite valIsNewIsUnique x y in rewrite disjointUnique z w in Refl

export
snocDisjoint : {x, y : BindingKeys} -> {valIsNew : _} -> Disjoint x y -> SetMissing newVal y -> Disjoint (snoc x newVal valIsNew) y
snocDisjoint EmptyDisjoint missing = EmptyDisjoint
snocDisjoint (AddDisjoint headMissing tailDisjoint) (ConsMissing newVal head elemNotHead elemNotInTail) = AddDisjoint (snocMissing head x newVal headMissing (symNeq elemNotHead)) (snocDisjoint tailDisjoint elemNotInTail)

inBoundsToSnocInbounds : {init : BindingKeys} -> {last : String} -> {lastMissing : SetMissing last init} -> {ind : Nat} -> InBounds ind init -> InBounds ind (snoc init last lastMissing)
inBoundsToSnocInbounds {init = (AddElement newVal set valIsNew)} {lastMissing = (ConsMissing last newVal elemNotHead elemNotInTail)}  InFirst = InFirst
inBoundsToSnocInbounds {init = (AddElement newVal set valIsNew)} {lastMissing = (ConsMissing last newVal elemNotHead elemNotInTail)} (InLater inBounds) = InLater (inBoundsToSnocInbounds inBounds)

indexIsIndexSnoc : {init : BindingKeys} -> {last : String} -> {lastMissing : SetMissing last init} -> (ind : Nat) -> (inBounds : InBounds ind init) ->
                   index ind init = index ind {ok = inBoundsToSnocInbounds {lastMissing} inBounds} (snoc init last lastMissing)
indexIsIndexSnoc 0 InFirst {lastMissing = (ConsMissing last head elemNotHead elemNotInTail)} = Refl
indexIsIndexSnoc (S k) (InLater inBounds) {lastMissing = (ConsMissing last head elemNotHead elemNotInTail)} = indexIsIndexSnoc k inBounds

getIndexOfSnoc : (init : BindingKeys) -> {0 last : String} -> (lastMissing : SetMissing last init) -> IndexData last (snoc init last lastMissing)
getIndexOfSnoc EmptySet EmptyMissing = (0 ** InFirst ** Refl)
getIndexOfSnoc (AddElement newVal set valIsNew) (ConsMissing last newVal elemNotHead elemNotInTail) =
  let (ind ** inBounds ** isInd) = getIndexOfSnoc set elemNotInTail in
      (S ind ** InLater inBounds ** isInd)

public export
append : (x, y : BindingKeys) -> Disjoint x y -> BindingKeys
append x EmptySet EmptyDisjoint = x
append x (AddElement newVal set valIsNew) (AddDisjoint newValMissing setDisjoint) = append (snoc x newVal newValMissing) set (snocDisjoint setDisjoint valIsNew)

export
appendMissingNew : {0 newVal : String} -> {x : BindingKeys} -> (set : BindingKeys) -> SetMissing newVal set -> (setDisjoint : Disjoint x set) -> SetMissing newVal x -> SetMissing newVal (append x set setDisjoint)
appendMissingNew EmptySet EmptyMissing EmptyDisjoint xMissing = xMissing
appendMissingNew (AddElement head tail existingSetMissing) (ConsMissing newVal head elemNotHead elemNotInTail) (AddDisjoint headMissing tailDisjoint) xMissing = appendMissingNew tail elemNotInTail (snocDisjoint tailDisjoint existingSetMissing) (snocMissing newVal x head xMissing elemNotHead)

export
appendMissingToBothMissing : {a : BindingKeys} -> (b : BindingKeys) -> (abDisjoint : Disjoint a b) -> SetMissing val (append a b abDisjoint) -> (SetMissing val a, SetMissing val b)
appendMissingToBothMissing EmptySet EmptyDisjoint appMissing = (appMissing, EmptyMissing)
appendMissingToBothMissing (AddElement newVal set valIsNew) (AddDisjoint aMissingNewVal aDisjointSet) appMissing = let (fstMissing, sndMissing) = appendMissingToBothMissing set (snocDisjoint aDisjointSet valIsNew) appMissing in
                                                                                                                       (snocMissingInv val a newVal fstMissing, ConsMissing val newVal (snocMissingInvNeq val a newVal fstMissing) sndMissing)

export
appendEmptyRightNeutral : (0 x : BindingKeys) -> {0 disjoint : Disjoint x EmptySet} -> append x EmptySet disjoint = x
appendEmptyRightNeutral x {disjoint = EmptyDisjoint} = Refl

export
lengthAppendIsSumLength : (x, y : BindingKeys) -> {disjoint : Disjoint x y} -> length (append x y disjoint) = length x + length y 
lengthAppendIsSumLength x EmptySet {disjoint = EmptyDisjoint} = sym $ plusZeroRightNeutral (length x)
lengthAppendIsSumLength x (AddElement newVal set valIsNew) {disjoint = (AddDisjoint xMissingNewVal z)} = trans (lengthAppendIsSumLength (snoc x newVal xMissingNewVal) set {disjoint = snocDisjoint z valIsNew {valIsNew = xMissingNewVal}}) (rewrite lengthSnocSucc x newVal xMissingNewVal in plusSuccRightSucc (length x) (length set))

export
appendConsLeftIsConsAppend : (x, y : BindingKeys) -> {disjoint : Disjoint x y} -> {newVal : String} -> {valIsNewX : SetMissing newVal x} -> {valIsNewY : SetMissing newVal y} -> append (AddElement newVal x valIsNewX) y (symDisjoint (AddDisjoint valIsNewY (symDisjoint disjoint))) = AddElement newVal (append x y disjoint) (appendMissingNew y valIsNewY disjoint valIsNewX)
appendConsLeftIsConsAppend x EmptySet {disjoint = EmptyDisjoint} = rewrite valIsNewIsUnique (appendMissingNew EmptySet valIsNewY EmptyDisjoint valIsNewX) valIsNewX in Refl
appendConsLeftIsConsAppend x (AddElement new2 y yMissingNew2) {disjoint = (AddDisjoint xMissingNew2 disjoint)} {valIsNewY} with (symDisjoint (AddDisjoint valIsNewY {valIsNew = valIsNewX} (symDisjoint (AddDisjoint xMissingNew2 disjoint))))
  appendConsLeftIsConsAppend x (AddElement new2 y yMissingNew2) {disjoint = (AddDisjoint xMissingNew2 disjoint)} {valIsNewY = (ConsMissing newVal new2 z valIsNewY)} | (AddDisjoint (ConsMissing new2 newVal elemNotHead elemNotInTail) w) =
    rewrite (disjointUnique (snocDisjoint w yMissingNew2 {valIsNew = ConsMissing new2 newVal elemNotHead elemNotInTail}) (symDisjoint (AddDisjoint valIsNewY (symDisjoint (snocDisjoint disjoint yMissingNew2 {valIsNew = elemNotInTail})) {valIsNew = snocMissing newVal x new2 valIsNewX (symNeq elemNotHead)}))) in rewrite valIsNewIsUnique xMissingNew2 elemNotInTail in rewrite neqUnique z (symNeq elemNotHead) in appendConsLeftIsConsAppend (snoc x new2 elemNotInTail) y {disjoint = (snocDisjoint disjoint yMissingNew2)} {newVal = newVal} {valIsNewX = (snocMissing newVal x new2 valIsNewX (symNeq elemNotHead))} {valIsNewY}

export
appendEmptyLeftNeutral : (y : BindingKeys) -> {0 disjoint : _} -> append EmptySet y disjoint = y
appendEmptyLeftNeutral EmptySet {disjoint = EmptyDisjoint} = Refl
appendEmptyLeftNeutral (AddElement newVal set valIsNew) {disjoint = (AddDisjoint emptyMissing emptyDisjointSet)} =
  rewrite valIsNewIsUnique emptyMissing EmptyMissing in rewrite disjointUnique (snocDisjoint emptyDisjointSet valIsNew {valIsNew = EmptyMissing}) (symDisjoint (AddDisjoint valIsNew EmptyDisjoint)) in trans (appendConsLeftIsConsAppend EmptySet set {newVal} {valIsNewX = EmptyMissing} {valIsNewY = valIsNew} {disjoint = emptyDisjointSet}) $ rewrite appendEmptyLeftNeutral set {disjoint = emptyDisjointSet} in cong (AddElement newVal set) (valIsNewIsUnique (replace {p = (\x => SetMissing newVal x)} (appendEmptyLeftNeutral set) (appendMissingNew set valIsNew emptyDisjointSet EmptyMissing)) valIsNew)

inBoundsToInboundsAppendLeft : (keys : BindingKeys) -> (keys2 : BindingKeys) -> {disjoint : Disjoint keys keys2} -> (ind : Nat) -> (inBounds : InBounds ind keys) -> InBounds ind (append keys keys2 disjoint)
inBoundsToInboundsAppendLeft keys EmptySet ind inBounds {disjoint = EmptyDisjoint} = inBounds
inBoundsToInboundsAppendLeft keys (AddElement newVal set valIsNew) ind inBounds {disjoint = (AddDisjoint keysMissingNewVal keysDisjointSet)} =
  inBoundsToInboundsAppendLeft (snoc keys newVal keysMissingNewVal) set ind (inBoundsToSnocInbounds inBounds)

indexFstIsIndexAppendLeft : (keys : BindingKeys) -> (keys2 : BindingKeys) -> {disjoint : Disjoint keys keys2} -> (ind : Nat) -> (inBounds : InBounds ind keys) -> index ind keys = index ind {ok = inBoundsToInboundsAppendLeft keys keys2 {disjoint} ind inBounds} (append keys keys2 disjoint)
indexFstIsIndexAppendLeft keys EmptySet ind inBounds {disjoint = EmptyDisjoint} = Refl
indexFstIsIndexAppendLeft keys (AddElement newVal set valIsNew) ind inBounds {disjoint = (AddDisjoint keysMissingNewVal keysDisjointSet)} = trans (indexIsIndexSnoc ind inBounds) (indexFstIsIndexAppendLeft (snoc keys newVal keysMissingNewVal) set ind (inBoundsToSnocInbounds inBounds))

export
indToAppendLeftInd : (keys : BindingKeys) -> (keys2 : BindingKeys) -> {disjoint : Disjoint keys keys2} -> (ind : Nat) -> {var : String} -> (inBounds : InBounds ind keys) -> (isInd : var = index ind keys) -> (inBounds : InBounds ind (append keys keys2 disjoint) ** var = index ind (append keys keys2 disjoint))
indToAppendLeftInd keys keys2 ind inBounds isInd = (inBoundsToInboundsAppendLeft keys keys2 ind inBounds ** trans isInd (indexFstIsIndexAppendLeft keys keys2 ind inBounds))

inBoundsToInboundsAppendRight : (keys : BindingKeys) -> (keys2 : BindingKeys) -> {disjoint : Disjoint keys keys2} -> (ind : Nat) -> (inBounds : InBounds ind keys2) -> InBounds (length keys + ind) (append keys keys2 disjoint)
inBoundsToInboundsAppendRight EmptySet keys2 ind inBounds = rewrite appendEmptyLeftNeutral keys2 {disjoint} in inBounds
inBoundsToInboundsAppendRight (AddElement newVal set valIsNew) keys2 ind inBounds with (symDisjoint disjoint)
  inBoundsToInboundsAppendRight (AddElement newVal set valIsNew) keys2 ind inBounds | (AddDisjoint keys2MissingNewVal disjoint') = rewrite (disjointUnique disjoint (symDisjoint (AddDisjoint keys2MissingNewVal (symDisjoint (symDisjoint disjoint'))))) in rewrite (appendConsLeftIsConsAppend set keys2 {disjoint = symDisjoint disjoint'} {newVal} {valIsNewX = valIsNew} {valIsNewY = keys2MissingNewVal}) in InLater (inBoundsToInboundsAppendRight set keys2 ind inBounds)

indexFstIsIndexAppendRight : (keys : BindingKeys) -> (keys2 : BindingKeys) -> {disjoint : Disjoint keys keys2} -> (ind : Nat) -> (inBounds : InBounds ind keys2) -> index ind keys2 = index (length keys + ind) {ok = inBoundsToInboundsAppendRight keys keys2 {disjoint} ind inBounds} (append keys keys2 disjoint)
indexFstIsIndexAppendRight EmptySet keys2 ind inBounds = rewrite appendEmptyLeftNeutral keys2 {disjoint} in Refl
indexFstIsIndexAppendRight (AddElement newVal set valIsNew) keys2 ind inBounds with (symDisjoint disjoint)
  indexFstIsIndexAppendRight (AddElement newVal set valIsNew) keys2 ind inBounds | (AddDisjoint keys2MissingNewVal disjoint') = rewrite (disjointUnique disjoint (symDisjoint (AddDisjoint keys2MissingNewVal (symDisjoint (symDisjoint disjoint'))))) in rewrite (appendConsLeftIsConsAppend set keys2 {disjoint = symDisjoint disjoint'} {newVal} {valIsNewX = valIsNew} {valIsNewY = keys2MissingNewVal}) in indexFstIsIndexAppendRight set keys2 ind inBounds

export
indToAppendRightInd : (keys : BindingKeys) -> (keys2 : BindingKeys) -> {disjoint : Disjoint keys keys2} -> (ind : Nat) -> {var : String} -> (inBounds : InBounds ind keys2) -> (isInd : var = index ind keys2) -> (inBounds : InBounds (length keys + ind) (append keys keys2 disjoint) ** var = index (length keys + ind) (append keys keys2 disjoint))
indToAppendRightInd keys keys2 ind inBounds isInd = (inBoundsToInboundsAppendRight keys keys2 {disjoint} ind inBounds ** trans isInd (indexFstIsIndexAppendRight keys keys2 ind inBounds))

public export
indAppendToIndEither : (keys : BindingKeys) -> (keys2 : BindingKeys) -> {disjoint : Disjoint keys keys2} -> (ind : Nat) -> {var : String} -> (inBounds : InBounds ind (append keys keys2 disjoint)) -> (isInd : var = index ind (append keys keys2 disjoint)) -> Either (inBounds : InBounds ind keys ** var = index ind keys) (IndexData var keys2)
indAppendToIndEither keys keys2 ind inBounds isInd with (getIndex var keys)
  indAppendToIndEither keys keys2 ind inBounds isInd | (Right (ind' ** inBounds' ** isInd')) = let (inBounds'' ** isInd'') = indToAppendLeftInd keys keys2 ind' inBounds' isInd' {disjoint} in
                                                                                                   Left (rewrite indexInjective {n = ind} {m = ind'} (trans (sym isInd) isInd'') in (inBounds' ** isInd'))
  indAppendToIndEither keys keys2 ind inBounds isInd | (Left keysMissingVar) with (getIndex var keys2)
    indAppendToIndEither keys keys2 ind inBounds isInd | (Left keysMissingVar) | (Right indData) = Right indData
    indAppendToIndEither keys keys2 ind inBounds isInd | (Left keysMissingVar) | (Left keys2MisssingVar) = void $ missingIndexAbsurd (append keys keys2 disjoint) ind inBounds isInd (appendMissingNew {x = keys} keys2 keys2MisssingVar disjoint keysMissingVar)

public export
data Elem : String -> BindingKeys -> Type where
  Here : Elem head (AddElement head tail missing)
  There : Elem key tail -> Elem key (AddElement head tail missing)

export
Uninhabited (Elem x EmptySet) where
  uninhabited Here impossible
  uninhabited (There x) impossible

isElem : (key : String) -> (set : BindingKeys) -> Either (SetMissing key set) (Elem key set)
isElem key EmptySet = Left EmptyMissing
isElem key (AddElement newVal set valIsNew) with (eitherNeqEq key newVal)
  isElem key (AddElement newVal set valIsNew) | (Right eq) = Right (rewrite eq in Here)
  isElem key (AddElement newVal set valIsNew) | (Left neq) with (isElem key set)
    isElem key (AddElement newVal set valIsNew) | (Left neq) | (Left missingTail) = Left (ConsMissing key newVal neq missingTail)
    isElem key (AddElement newVal set valIsNew) | (Left neq) | (Right elemTail) = Right (There elemTail)

missingElemAbsurd : SetMissing key set -> Elem key set -> Void
missingElemAbsurd (ConsMissing key key keyNotKey _) Here = neqToNotEqual keyNotKey Refl
missingElemAbsurd (ConsMissing key head _ keyNotInTail) (There elem) = missingElemAbsurd keyNotInTail elem

missingElemNeq : {x, y : String} -> SetMissing x set -> Elem y set -> NEQ x y
missingElemNeq missing elem with (eitherNeqEq x y)
  missingElemNeq missing elem | (Left neq) = neq
  missingElemNeq missing elem | (Right eq) = void $ missingElemAbsurd missing (rewrite eq in elem)

snocIsElem : (init : BindingKeys) -> {last : String} -> (missing : SetMissing last init) -> Elem last (snoc init last missing)
snocIsElem EmptySet _ = Here
snocIsElem (AddElement _ set _) (ConsMissing last newVal _ elemNotInTail) = There (snocIsElem set elemNotInTail)

export
indexDataToElem : IndexData val set -> Elem val set
indexDataToElem (0 ** InFirst ** Refl) = Here
indexDataToElem ((S ind) ** (InLater inBounds) ** isInd) = There (indexDataToElem (ind ** inBounds ** isInd))

elemToElemSnoc : Elem val init -> {missing : SetMissing last init} -> Elem val (snoc init last missing)
elemToElemSnoc Here {missing = (ConsMissing last val elemNotHead elemNotInTail)} = Here
elemToElemSnoc (There elem) {missing = (ConsMissing last head elemNotHead elemNotInTail)} = There (elemToElemSnoc elem)

public export
data Subset : BindingKeys -> BindingKeys -> Type where
  EmptySubset : Subset EmptySet set
  ConsSubset : Elem head set -> Subset tail set -> Subset (AddElement head tail missing) set

export
subsetAddRight : Subset x y -> Subset x (AddElement newElement y missing)
subsetAddRight EmptySubset = EmptySubset
subsetAddRight (ConsSubset elem subSet) = ConsSubset (There elem) (subsetAddRight subSet)

public export
Reflexive BindingKeys Subset where
  reflexive {x = EmptySet} = EmptySubset
  reflexive {x = (AddElement newVal set valIsNew)} = ConsSubset Here (subsetAddRight (reflexive {rel=Subset}))

elemSubsetIsElem : Elem val sub -> Subset sub set -> Elem val set
elemSubsetIsElem Here (ConsSubset elem _) = elem
elemSubsetIsElem (There elem) (ConsSubset _ subset) = elemSubsetIsElem elem subset

public export
Transitive BindingKeys Subset where
  transitive EmptySubset _ = EmptySubset
  transitive (ConsSubset elemX subX) subY = ConsSubset (elemSubsetIsElem elemX subY) (transitive {rel=Subset} subX subY)

export
missingSetMisssingSubset : {key : String} -> {sub : BindingKeys} -> SetMissing key set -> Subset sub set -> SetMissing key sub
missingSetMisssingSubset _ EmptySubset = EmptyMissing
missingSetMisssingSubset missing (ConsSubset elem subset) = ConsMissing key _ (missingElemNeq missing elem) (missingSetMisssingSubset missing subset)

subsetRemoveFirstRightMissing : Subset sub (AddElement elem set missing) -> SetMissing elem sub -> Subset sub set
subsetRemoveFirstRightMissing EmptySubset _ = EmptySubset
subsetRemoveFirstRightMissing (ConsSubset Here subset) (ConsMissing elem elem neq _) = void $ neqToNotEqual neq Refl
subsetRemoveFirstRightMissing (ConsSubset (There elemTail) subset) (ConsMissing elem head _ missing) = ConsSubset elemTail (subsetRemoveFirstRightMissing subset missing)

removeElem : {key : String} -> (set : BindingKeys) -> Elem key set ->
             (setOut : BindingKeys ** (Subset setOut set, length set = S (length setOut), {sub : BindingKeys} -> Subset sub set -> SetMissing key sub -> Subset sub setOut))
removeElem (AddElement key tail missing) Here = (tail ** (subsetAddRight (reflexive {rel=Subset}), Refl, subsetRemoveFirstRightMissing))
removeElem (AddElement head tail missing) (There elem) =
  let (removed ** (subset, smaller, stillSubFunc)) = removeElem tail elem
      subset' = ConsSubset Here (subsetAddRight subset)
      smaller' = cong S smaller in
  let stillSubFunc' : {sub : BindingKeys} -> Subset sub (AddElement head tail missing) -> SetMissing key sub -> Subset sub (AddElement head removed (missingSetMisssingSubset missing subset))
      stillSubFunc' EmptySubset missing = EmptySubset
      stillSubFunc' (ConsSubset Here sub) (ConsMissing _ _ _ missing) = ConsSubset Here (stillSubFunc' sub missing)
      stillSubFunc' {sub = AddElement subHead subTail subHeadMissing} (ConsSubset (There elem) sub) (ConsMissing _ _ neq missing) =
        let (ConsSubset elem' sub') = stillSubFunc (ConsSubset elem EmptySubset {missing = EmptyMissing}) (ConsMissing key subHead neq EmptyMissing)
            stillSub' = stillSubFunc' sub missing
         in ConsSubset (There elem') stillSub'
   in (AddElement head removed (missingSetMisssingSubset missing subset) ** (subset', smaller', stillSubFunc'))

export
subsetSmallerOrSameSize : {x, y : BindingKeys} -> Subset x y -> length x `LTE` length y
subsetSmallerOrSameSize EmptySubset = LTEZero
subsetSmallerOrSameSize (ConsSubset elem subset {missing}) =
  let (removed ** (_, smaller, stillSubFunc)) = removeElem y elem
   in rewrite smaller in LTESucc $ subsetSmallerOrSameSize (stillSubFunc subset missing)

snocIsSubset : (init : BindingKeys) -> {0 last : String} -> (missing : SetMissing last init) -> Subset init (snoc init last missing)
snocIsSubset EmptySet missing = EmptySubset
snocIsSubset (AddElement newVal set valIsNew) (ConsMissing last newVal elemNotHead elemNotInTail) = ConsSubset Here (subsetAddRight (snocIsSubset set elemNotInTail))

snocSubset : (Subset init set) -> (Elem last set) -> {missing : SetMissing last init} -> Subset (snoc init last missing) set
snocSubset EmptySubset elemLast = ConsSubset elemLast EmptySubset
snocSubset (ConsSubset elem subset) elemLast {missing = (ConsMissing last head elemNotHead elemNotInTail)} = ConsSubset elem (snocSubset subset elemLast)

record Equivalent (x : BindingKeys) (y : BindingKeys) where
  constructor IsEquivalent
  subLeft  : Subset x y
  subRight : Subset y x

export
union : BindingKeys -> BindingKeys -> BindingKeys
union x EmptySet = x
union x (AddElement newVal set valIsNew) with (getIndex newVal x)
  union x (AddElement newVal set valIsNew) | (Left xMissingNewVal) = union (snoc x newVal xMissingNewVal) set
  union x (AddElement newVal set valIsNew) | (Right _) = union x set

export
unionDisjointIsAppend : (x, y : BindingKeys) -> (disjoint : Disjoint x y) -> union x y = append x y disjoint
unionDisjointIsAppend x EmptySet EmptyDisjoint = Refl
unionDisjointIsAppend x (AddElement newVal set valIsNew) (AddDisjoint xMissingNewVal xDisjointSet) with (getIndex newVal x)
  unionDisjointIsAppend x (AddElement newVal set valIsNew) (AddDisjoint xMissingNewVal xDisjointSet) | (Left xMissingNewVal') = rewrite valIsNewIsUnique xMissingNewVal' xMissingNewVal in unionDisjointIsAppend _ set (snocDisjoint xDisjointSet valIsNew)
  unionDisjointIsAppend x (AddElement newVal set valIsNew) (AddDisjoint xMissingNewVal xDisjointSet) | (Right (index ** inBounds ** isIndex)) = void $ missingIndexAbsurd x index inBounds isIndex xMissingNewVal

export
missingUnionMissingLeft : (x, y : BindingKeys) -> SetMissing k (union x y) -> SetMissing k x
missingUnionMissingLeft x EmptySet isMissing = isMissing
missingUnionMissingLeft x (AddElement newVal set valIsNew) isMissing with (getIndex newVal x)
  missingUnionMissingLeft x (AddElement newVal set valIsNew) isMissing | (Left xMissingNewVal) = snocMissingInv k x newVal (missingUnionMissingLeft (snoc x newVal xMissingNewVal) set isMissing)
  missingUnionMissingLeft x (AddElement newVal set valIsNew) isMissing | (Right _) = missingUnionMissingLeft x set isMissing

missingInIndexNeq : SetMissing k set -> (ind : Nat) -> (inBounds : InBounds ind set) -> l = index ind set {ok = inBounds} -> NEQ k l
missingInIndexNeq (ConsMissing k head elemNotHead _) 0 InFirst prf = rewrite prf in elemNotHead
missingInIndexNeq (ConsMissing k head _ elemNotInTail) (S ind) (InLater inBounds) prf = missingInIndexNeq elemNotInTail ind inBounds prf

export
missingUnionMissingRight : (x, y : BindingKeys) -> SetMissing k (union x y) -> SetMissing k y
missingUnionMissingRight x EmptySet _ = EmptyMissing
missingUnionMissingRight x (AddElement newVal set valIsNew) isMissing with (getIndex newVal x)
  missingUnionMissingRight x (AddElement newVal set valIsNew) isMissing | (Left xMissingNewVal) =
    let snocMissing = missingUnionMissingLeft (snoc x newVal xMissingNewVal) set isMissing
        headNeq = snocMissingInvNeq k x newVal snocMissing
        missingTail = missingUnionMissingRight (snoc x newVal xMissingNewVal) set isMissing in
        ConsMissing k newVal headNeq missingTail
  missingUnionMissingRight x (AddElement newVal set valIsNew) isMissing | (Right (ind ** inBounds ** isInd)) =
    let leftMissing = missingUnionMissingLeft x set isMissing
        headNeq = missingInIndexNeq leftMissing ind inBounds isInd
        missingTail = missingUnionMissingRight x set isMissing in
        ConsMissing k newVal headNeq missingTail

export
elemLeftElemUnion : (x, y : BindingKeys) -> Elem k x -> Elem k (union x y)
elemLeftElemUnion x EmptySet elem = elem
elemLeftElemUnion x (AddElement newVal set valIsNew) elem with (getIndex newVal x)
  elemLeftElemUnion x (AddElement newVal set valIsNew) elem | (Left xMissingNew) = elemLeftElemUnion _ _ (elemToElemSnoc elem)
  elemLeftElemUnion x (AddElement newVal set valIsNew) elem | (Right _) = elemLeftElemUnion x set elem

export
elemRightElemUnion : (x, y : BindingKeys) -> Elem k y -> Elem k (union x y)
elemRightElemUnion x (AddElement k tail missing) Here with (getIndex k x)
  elemRightElemUnion x (AddElement k tail missing) Here | (Left xMissingK) = elemLeftElemUnion _ _ (snocIsElem x xMissingK)
  elemRightElemUnion x (AddElement k tail missing) Here | (Right index) = elemLeftElemUnion x tail (indexDataToElem index)
elemRightElemUnion x (AddElement head tail missing) (There elem) with (getIndex head x)
  elemRightElemUnion x (AddElement head tail missing) (There elem) | (Left xMissingHead) = elemRightElemUnion _ _ elem
  elemRightElemUnion x (AddElement head tail missing) (There elem) | (Right _) = elemRightElemUnion x tail elem

snocUnionIsUnionSnoc : (x, y : BindingKeys) -> {newVal : String} -> (isMissing : SetMissing newVal (union x y)) -> snoc (union x y) newVal isMissing = union x (snoc y newVal (missingUnionMissingRight x y isMissing))
snocUnionIsUnionSnoc x EmptySet isMissing with (getIndex newVal x)
  snocUnionIsUnionSnoc x EmptySet isMissing | (Left isMissing') = rewrite valIsNewIsUnique isMissing' isMissing in Refl
  snocUnionIsUnionSnoc x EmptySet isMissing | (Right (ind ** inBounds ** isInd)) = void $ missingIndexAbsurd x ind inBounds isInd isMissing
snocUnionIsUnionSnoc x (AddElement newVal' set valIsNew) isMissing with (missingUnionMissingRight x (AddElement newVal' set valIsNew) isMissing)
  snocUnionIsUnionSnoc x (AddElement newVal' set valIsNew) isMissing | (ConsMissing newVal newVal' elemNotHead elemNotInTail) with (getIndex newVal' x)
    snocUnionIsUnionSnoc x (AddElement newVal' set valIsNew) isMissing | (ConsMissing newVal newVal' elemNotHead elemNotInTail) | (Left xMissingPrime) =
      rewrite valIsNewIsUnique elemNotInTail (missingUnionMissingRight _ set isMissing) in
              snocUnionIsUnionSnoc _ set isMissing
    snocUnionIsUnionSnoc x (AddElement newVal' set valIsNew) isMissing | (ConsMissing newVal newVal' elemNotHead elemNotInTail) | (Right _) =
      rewrite valIsNewIsUnique elemNotInTail (missingUnionMissingRight _ set isMissing) in
              snocUnionIsUnionSnoc x set isMissing

unionIndexIsUnionSnoc : (x, y : BindingKeys) -> {newVal : String} -> (ind : Nat) -> (inBounds : InBounds ind (union x y)) -> (isIndex : newVal = index ind (union x y)) -> (isMissing : SetMissing newVal y) ->
                        union x y = union x (snoc y newVal isMissing)
unionIndexIsUnionSnoc x EmptySet ind inBounds isIndex isMissing with (getIndex newVal x)
  unionIndexIsUnionSnoc x EmptySet ind inBounds isIndex isMissing | (Left xMissingNewVal) = void $ missingIndexAbsurd x ind inBounds isIndex xMissingNewVal
  unionIndexIsUnionSnoc x EmptySet _ _ _ _ | (Right _) = Refl
unionIndexIsUnionSnoc x (AddElement newVal' set valIsNew) ind inBounds isIndex (ConsMissing newVal newVal' elemNotHead elemNotInTail) with (getIndex newVal' x)
  unionIndexIsUnionSnoc x (AddElement newVal' set valIsNew) ind inBounds isIndex (ConsMissing newVal newVal' elemNotHead elemNotInTail) | (Left xMissingPrime) =
    unionIndexIsUnionSnoc (snoc x newVal' xMissingPrime) set ind inBounds isIndex elemNotInTail
  unionIndexIsUnionSnoc x (AddElement newVal' set valIsNew) ind inBounds isIndex (ConsMissing newVal newVal' elemNotHead elemNotInTail) | (Right _) =
    unionIndexIsUnionSnoc x set ind inBounds isIndex elemNotInTail

export
unionAssociative : (x, y, z : BindingKeys) -> union (union x y) z = union x (union y z)
unionAssociative x y EmptySet = Refl
unionAssociative x y (AddElement newVal set valIsNew) with (getIndex newVal y)
  unionAssociative x y (AddElement newVal set valIsNew) | (Left yMissingNewVal) with (getIndex newVal (union x y))
    unionAssociative x y (AddElement newVal set valIsNew) | (Left yMissingNewVal) | (Left xyMissingNewVal) =
      rewrite snocUnionIsUnionSnoc x y xyMissingNewVal in
      rewrite valIsNewIsUnique (missingUnionMissingRight x y xyMissingNewVal) yMissingNewVal in
              unionAssociative x (snoc y newVal yMissingNewVal) set
    unionAssociative x y (AddElement newVal set valIsNew) | (Left yMissingNewVal) | (Right (indXY ** inBoundsXY ** isIndXY)) =
      rewrite unionIndexIsUnionSnoc x y indXY inBoundsXY isIndXY yMissingNewVal in
              unionAssociative x (snoc y newVal yMissingNewVal) set
  unionAssociative x y (AddElement newVal set valIsNew) | (Right (indY ** inBoundsY ** isIndY)) with (getIndex newVal (union x y))
    unionAssociative x y (AddElement newVal set valIsNew) | (Right (indY ** inBoundsY ** isIndY)) | (Left xyMissingNewVal) = void $ missingIndexAbsurd y indY inBoundsY isIndY (missingUnionMissingRight x y xyMissingNewVal)
    unionAssociative x y (AddElement newVal set valIsNew) | (Right (indY ** inBoundsY ** isIndY)) | (Right _) = unionAssociative x y set

export
missingBothMissingUnion : (x, y : BindingKeys) -> SetMissing k x -> SetMissing k y -> SetMissing k (union x y)
missingBothMissingUnion x EmptySet missingX _ = missingX
missingBothMissingUnion x (AddElement newVal set valIsNew) missingX (ConsMissing k newVal elemNotHead elemNotInTail) with (getIndex newVal x)
  missingBothMissingUnion x (AddElement newVal set valIsNew) missingX (ConsMissing k newVal elemNotHead elemNotInTail) | (Left xMissingNewVal) =
    let snocIsMissing = snocMissing k x newVal missingX elemNotHead in 
        missingBothMissingUnion (snoc x newVal xMissingNewVal) set snocIsMissing elemNotInTail
  missingBothMissingUnion x (AddElement newVal set valIsNew) missingX (ConsMissing k newVal elemNotHead elemNotInTail) | (Right _) = missingBothMissingUnion x set missingX elemNotInTail

unionEmptyLeftNeutral : (x : BindingKeys) -> union EmptySet x = x
unionEmptyLeftNeutral x = rewrite unionDisjointIsAppend EmptySet x (symDisjoint EmptyDisjoint) in appendEmptyLeftNeutral x {disjoint = symDisjoint EmptyDisjoint}

unionIndexedSnocRightNeutral : (x, y : BindingKeys) -> {val : String} -> (ind : Nat) -> (inBounds : InBounds ind x) -> (isInd : val = index ind x) -> (missing : SetMissing val y) ->
                               union x y = union x (snoc y val missing)
unionIndexedSnocRightNeutral x EmptySet ind inBounds isInd missing with (getIndex val x)
  unionIndexedSnocRightNeutral x EmptySet ind inBounds isInd missing | (Left xMissing) = void $ missingIndexAbsurd x ind inBounds isInd xMissing
  unionIndexedSnocRightNeutral x EmptySet ind inBounds isInd missing | (Right _) = Refl
unionIndexedSnocRightNeutral x (AddElement newVal set valIsNew) ind inBounds isInd (ConsMissing val newVal _ elemNotInTail)with (getIndex newVal x)
  unionIndexedSnocRightNeutral x (AddElement newVal set valIsNew) ind inBounds isInd (ConsMissing val newVal _ elemNotInTail) | (Left xMissing) =
    let snocIsInd = trans isInd (indexIsIndexSnoc ind inBounds) in
        unionIndexedSnocRightNeutral (snoc x newVal xMissing) set ind (inBoundsToSnocInbounds inBounds) snocIsInd elemNotInTail
  unionIndexedSnocRightNeutral x (AddElement newVal set valIsNew) ind inBounds isInd (ConsMissing val newVal _ elemNotInTail) | (Right _) =
    unionIndexedSnocRightNeutral x set ind inBounds isInd elemNotInTail

export
unionLeftIsSub : (x, y : BindingKeys) -> Subset x (union x y)
unionLeftIsSub x EmptySet = reflexive {rel=Subset}
unionLeftIsSub x (AddElement newVal set valIsNew) with (getIndex newVal x)
  unionLeftIsSub x (AddElement newVal set valIsNew) | (Left xMissingNewVal) = transitive {rel=Subset} (snocIsSubset x xMissingNewVal) (unionLeftIsSub (snoc x newVal xMissingNewVal) set)
  unionLeftIsSub x (AddElement newVal set valIsNew) | (Right _) = unionLeftIsSub x set

export
unionRightIsSub : (x, y : BindingKeys) -> Subset y (union x y)
unionRightIsSub x EmptySet = EmptySubset
unionRightIsSub x (AddElement newVal set valIsNew) with (getIndex newVal x)
  unionRightIsSub x (AddElement newVal set valIsNew) | (Left xMissingNewVal) =
    let leftSub = unionLeftIsSub (snoc x newVal xMissingNewVal) set
        rightSub = unionRightIsSub (snoc x newVal xMissingNewVal) set
     in ConsSubset (elemSubsetIsElem (snocIsElem x xMissingNewVal) leftSub) rightSub
  unionRightIsSub x (AddElement newVal set valIsNew) | (Right index) =
    let leftSub = unionLeftIsSub x set
        rightSub = unionRightIsSub x set
     in ConsSubset (elemSubsetIsElem (indexDataToElem index) leftSub) rightSub

--lengthUnionIndexedAppendRightSame : (x, y : BindingKeys) -> {val : String} -> (ind : Nat) -> (inBounds : InBounds ind y) -> (isInd : val = index ind y) -> (missing : SetMissing val x) ->
--                                    length (union x y) = length (union (AddElement val x missing) y)
--lengthUnionIndexedAppendRightSame x (AddElement head set headIsNew) 0 InFirst isInd missing with (eitherNeqEq head val)
--  lengthUnionIndexedAppendRightSame x (AddElement head set headIsNew) 0 InFirst isInd missing | (Left neq) = void $ neqToNotEqual neq (sym isInd)
--  lengthUnionIndexedAppendRightSame x (AddElement head set headIsNew) 0 InFirst isInd missing | (Right _) with (getIndex head x)
--    lengthUnionIndexedAppendRightSame x (AddElement head set headIsNew) 0 InFirst isInd missing | (Right _) | (Left xMissingHead) = ?lengthUnionIndexedAppendRightSame_rhs_1
--    lengthUnionIndexedAppendRightSame x (AddElement head set headIsNew) 0 InFirst isInd missing | (Right _) | (Right (ind' ** inBounds' ** isInd')) = void $ missingIndexAbsurd _ ind' inBounds' (trans isInd isInd') missing
--lengthUnionIndexedAppendRightSame x (AddElement head set headIsNew) (S k) (InLater z) isInd missing = ?lengthUnionIndexedAppendRightSame_rhs_2

export
subsetLeftSubsetUnion : (x, y, right : BindingKeys) -> Subset x y -> Subset (union x right) (union y right)
subsetLeftSubsetUnion x y EmptySet subset = subset
subsetLeftSubsetUnion x y (AddElement newVal set valIsNew) subset with (getIndex newVal x)
  subsetLeftSubsetUnion x y (AddElement newVal set valIsNew) subset | (Left xMissingNewVal) with (getIndex newVal y)
    subsetLeftSubsetUnion x y (AddElement newVal set valIsNew) subset | (Left xMissingNewVal) | (Left yMissingNewVal) =
      subsetLeftSubsetUnion (snoc x newVal xMissingNewVal) (snoc y newVal yMissingNewVal) set (snocSubset (transitive {rel=Subset} subset (snocIsSubset y yMissingNewVal)) (snocIsElem y yMissingNewVal))
    subsetLeftSubsetUnion x y (AddElement newVal set valIsNew) subset | (Left xMissingNewVal) | (Right indexY) =
      subsetLeftSubsetUnion (snoc x newVal xMissingNewVal) y set (snocSubset subset (indexDataToElem indexY))
  subsetLeftSubsetUnion x y (AddElement newVal set valIsNew) subset | (Right _) with (getIndex newVal y)
    subsetLeftSubsetUnion x y (AddElement newVal set valIsNew) subset | (Right _) | (Left yMissingNewVal) =
      subsetLeftSubsetUnion x (snoc y newVal yMissingNewVal) set (transitive {rel=Subset} subset (snocIsSubset y yMissingNewVal))
    subsetLeftSubsetUnion x y (AddElement newVal set valIsNew) subset | (Right _) | (Right _) =
      subsetLeftSubsetUnion x y set subset

export
unionSubsetSym : (x, y : BindingKeys) -> Subset (union x y) (union y x)
unionSubsetSym x EmptySet = unionRightIsSub EmptySet x
unionSubsetSym x (AddElement newVal set valIsNew) with (getIndex newVal x)
  unionSubsetSym x (AddElement newVal set valIsNew) | (Left xMissingNewVal) =
    let subSym = unionSubsetSym (snoc x newVal xMissingNewVal) set
        reorganizeSub = rewrite unionIndexedSnocRightNeutral (AddElement newVal set valIsNew) x 0 InFirst Refl xMissingNewVal in
                                subsetLeftSubsetUnion _ _ _ (subsetAddRight (reflexive {rel=Subset}))
     in transitive {rel=Subset} subSym reorganizeSub
  unionSubsetSym x (AddElement newVal set valIsNew) | (Right index) =
    let subSym = unionSubsetSym x set
        reorganizeSub = subsetLeftSubsetUnion _ _ _ (subsetAddRight (reflexive {rel=Subset}))
     in transitive {rel=Subset} subSym reorganizeSub

export
subsetRightSubsetUnion : (x, y, left : BindingKeys) -> Subset x y -> Subset (union left x) (union left y)
subsetRightSubsetUnion x y left xSubY = transitive {rel=Subset} (unionSubsetSym left x) $ transitive {rel=Subset} (subsetLeftSubsetUnion x y left xSubY) (unionSubsetSym y left)

export
lengthUnionSymSame : (x, y : BindingKeys) -> length (union x y) = length (union y x)
lengthUnionSymSame x y = let smallerxyyx = subsetSmallerOrSameSize $ unionSubsetSym x y
                             smalleryxxy = subsetSmallerOrSameSize $ unionSubsetSym y x
                          in antisymmetric {rel=LTE} smallerxyyx smalleryxxy

export
unionBiggerOrSameLeft : (x, y : BindingKeys) -> length x `LTE` length (union x y)
unionBiggerOrSameLeft x y = subsetSmallerOrSameSize (unionLeftIsSub x y)

export
unionBiggerOrSameRight : (x, y : BindingKeys) -> length y `LTE` length (union x y)
unionBiggerOrSameRight x y = subsetSmallerOrSameSize (unionRightIsSub x y)

export
unionSubsetRightEqual : (x, y : BindingKeys) -> Subset y x -> union x y = x
unionSubsetRightEqual x EmptySet EmptySubset = Refl
unionSubsetRightEqual x (AddElement head tail missing) (ConsSubset elem subset) with (getIndex head x)
  unionSubsetRightEqual x (AddElement head tail _) (ConsSubset elem _) | (Left xMissingHead) = void $ missingElemAbsurd xMissingHead elem
  unionSubsetRightEqual x (AddElement head tail _) (ConsSubset _ subset) | (Right _) = unionSubsetRightEqual x tail subset

export
unionsSubsetSubset : (w, x, y : BindingKeys) -> Subset w y -> Subset x y -> Subset (union w x) y
unionsSubsetSubset w EmptySet y wSubY EmptySubset = wSubY
unionsSubsetSubset w (AddElement head tail missing) y wSubY (ConsSubset headElemY tailSubY) with (getIndex head w)
  unionsSubsetSubset w (AddElement head tail missing) y wSubY (ConsSubset headElemY tailSubY) | (Left wMissingHead) =
    let consSubY = snocSubset wSubY headElemY
     in unionsSubsetSubset (snoc w head wMissingHead) tail y consSubY tailSubY
  unionsSubsetSubset w (AddElement head tail missing) y wSubY (ConsSubset headElemY tailSubY) | (Right _) =
    unionsSubsetSubset w tail y wSubY tailSubY

export
unionsSubsetSubsetUnion : (w, x, y, z : BindingKeys) -> Subset w x -> Subset y z -> Subset (union w y) (union x z)
unionsSubsetSubsetUnion w x y z wSubX ySubZ =
  let leftSub = transitive {rel=Subset} wSubX (unionLeftIsSub x z)
      rightSub = transitive {rel=Subset} ySubZ (unionRightIsSub x z)
   in unionsSubsetSubset w y (union x z) leftSub rightSub

--snocSubset : (Subset init set) -> (Elem last set) -> {missing : SetMissing last init} -> Subset (snoc init last missing) set

--unionsSmallerEqSmallerIsSmaller : (w, x, y, z : BindingKeys) -> (length w) `LT` (length x) -> (length y) `LTE` (length z) -> (length (union w y)) `LT` (length (union x z))
--
--unionsSmallerSmallerEqIsSmaller : (w, x, y, z : BindingKeys) -> (length w) `LTE` (length x) -> (length y) `LT` (length z) -> (length (union w y)) `LT` (length (union x z))
--unionsSmallerSmallerEqIsSmaller w x y EmptySet _ ySmallerOrEqualZ = absurd ySmallerOrEqualZ
--unionsSmallerSmallerEqIsSmaller w x y (AddElement newVal set valIsNew) wSmallerOrEqualX (LTESucc ySmallerOrEqualSet) with (getIndex newVal x)
--  unionsSmallerSmallerEqIsSmaller w x y (AddElement newVal set valIsNew) wSmallerOrEqualX (LTESucc ySmallerOrEqualSet) | (Left xMissingNewVal) =
--    let wSmallerSnocX = rewrite lengthSnocSucc x newVal xMissingNewVal in LTESucc wSmallerOrEqualX
--     in unionsSmallerEqSmallerIsSmaller w (snoc x newVal xMissingNewVal) y set wSmallerSnocX ySmallerOrEqualSet
--  unionsSmallerSmallerEqIsSmaller w x y (AddElement newVal set valIsNew) wSmallerOrEqualX (LTESucc ySmallerOrEqualSet) | (Right _) = ?unionsSmallerSmaller_rhs_2

--unionsSmallerSmaller w x EmptySet EmptySet _ ySmallerOrEqualZ = absurd ySmallerOrEqualZ
--unionsSmallerSmaller w x EmptySet (AddElement newVal set valIsNew) wSmallery _ with (getIndex newVal x)
--  unionsSmallerSmaller w x EmptySet (AddElement newVal set valIsNew) wSmallery _ | (Left xMissingNewVal) = ?unionsSmallerSmaller_rhs_1 -- (unionsSmallerSmaller w (snoc x newVal xMissingNewVal) EmptySet set ?abc ?def)
--  --unionsSmallerSmaller w x EmptySet (AddElement newVal set valIsNew) wSmallery _ | (Left xMissingNewVal) = ?unionsSmallerSmaller_rhs_1 -- (unionsSmallerSmaller w (snoc x newVal xMissingNewVal) EmptySet set ?abc ?def)
--  unionsSmallerSmaller w x EmptySet (AddElement newVal set valIsNew) wSmallery _ | (Right y) = ?unionsSmallerSmaller_rhs_3
--unionsSmallerSmaller w x (AddElement newVal set valIsNew) EmptySet wSmallery ySmallerOrEqualZ = ?unionsSmallerSmaller_rhs_4
--unionsSmallerSmaller w x (AddElement newVal set valIsNew) (AddElement y z v) wSmallery ySmallerOrEqualZ = ?unionsSmallerSmaller_rhs_5

difference : (a, b : BindingKeys) -> (diff : BindingKeys ** (Subset diff a, Disjoint b diff))
difference EmptySet b = (EmptySet ** (EmptySubset, EmptyDisjoint))
difference (AddElement newVal set valIsNew) b with (isElem newVal b)
  difference (AddElement newVal set valIsNew) b | (Left bMissingNewVal) = let (setDiff ** (sdSub, sdDisjoint)) = difference set b
                                                                           in (AddElement newVal setDiff (missingSetMisssingSubset valIsNew sdSub) ** (ConsSubset Here (subsetAddRight sdSub), AddDisjoint bMissingNewVal sdDisjoint))
  difference (AddElement newVal set valIsNew) b | (Right bElemNewVal) = let (setDiff ** (sdSub, sdDisjoint)) = difference set b
                                                                         in (setDiff ** (subsetAddRight sdSub, sdDisjoint))

export
(-) : (a, b : BindingKeys) -> BindingKeys
(-) a b = fst $ difference a b
