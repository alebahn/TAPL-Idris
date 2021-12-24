module Recon

import Data.DPair
import Data.Fin
import Data.Nat
import Data.Vect
import Data.Vect.Elem
import Data.Stream
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Decidable.Equality
import Control.WellFounded

import BindingKeys

%default total

data Ty = TyBool | TyArr Ty Ty | TyId String | TyNat

maybeEq : (x, y : Ty) -> Maybe (x = y)
maybeEq TyBool TyBool = Just Refl
maybeEq (TyArr w x) (TyArr y z) =
  do Refl <- maybeEq w y
     Refl <- maybeEq x z
     Just Refl
maybeEq (TyId x) (TyId y) with (decEq x y)
  maybeEq (TyId x) (TyId x) | (Yes Refl) = Just Refl
  maybeEq (TyId x) (TyId y) | (No contra) = Nothing
maybeEq TyNat TyNat = Just Refl
maybeEq _ _ = Nothing

eqNotNothing : (x, y : Ty) -> maybeEq x y = Nothing -> (x = y) -> Void
eqNotNothing TyBool TyBool eqNothing Refl = absurd eqNothing
eqNotNothing (TyArr x y) (TyArr x y) eqNothing Refl with (maybeEq x x) proof maybeXXprf
  eqNotNothing (TyArr x y) (TyArr x y) eqNothing Refl | Nothing = eqNotNothing x x maybeXXprf Refl
  eqNotNothing (TyArr x y) (TyArr x y) eqNothing Refl | (Just Refl) with (maybeEq y y) proof maybeYYprf
    eqNotNothing (TyArr x y) (TyArr x y) eqNothing Refl | (Just Refl) | Nothing = eqNotNothing y y maybeYYprf Refl
    eqNotNothing (TyArr x y) (TyArr x y) eqNothing Refl | (Just Refl) | (Just Refl) = absurd eqNothing
eqNotNothing (TyId x) (TyId x) eqNothing Refl with (decEq x x) proof prf
  eqNotNothing (TyId x) (TyId x) eqNothing Refl | (Yes Refl) = absurd eqNothing
  eqNotNothing (TyId x) (TyId x) _         Refl | (No contra) = contra Refl
eqNotNothing TyNat TyNat eqNothing Refl = absurd eqNothing

DecEq Ty where
  decEq a b with (maybeEq a b) proof maybeABprf
    decEq a b | (Just x) = Yes x
    decEq a b | Nothing = No (eqNotNothing a b maybeABprf)

namespace LList
  public export
  data LList : Type -> Type where
    Nil : LList a
    (::) : (1 _ : a) -> (1 _ : LList a) -> LList a

Constr : Type
Constr = List (Ty, Ty)

namespace HLStream
  public export
  data HLStream : Type -> Type where
    (::) : a -> (1 _ : Inf (HLStream a)) -> HLStream a

iterate : (a -> a) -> (acc : a) -> HLStream a
iterate f acc = acc :: iterate f (f acc)

Functor HLStream where
  map f (x :: y) = (f x) :: (map f y)

names : HLStream String
names = ("?X_" ++) <$> show <$> (iterate S Z)

data Term : Nat -> Type where
  TmVar : Fin n -> Term n
  TmAbs : (nm : String) -> (ty : Ty )-> (body : Term (S n)) -> Term n
  TmApp : Term n -> Term n -> Term n
  TmTrue : Term n
  TmFalse : Term n
  TmIf : (g : Term n) -> (t : Term n) -> (e : Term n) -> Term n
  TmZero : Term n
  TmSucc : Term n -> Term n
  TmPred : Term n -> Term n
  TmIsZero : Term n -> Term n

Context : Nat ->Type
Context n = Vect n (String, Ty)

recon : Context n -> (1 names : HLStream String) -> Term n -> LPair (HLStream String) (Ty, Constr)
recon context names (TmVar x) = (names # (snd (index x context), []))
recon context names (TmAbs nm ty body) = let (names' # (bTy, contr)) = recon ((nm, ty) :: context) names body in
                                             (names' # (TyArr ty bTy, contr))
recon context names (TmApp f arg) = let (names'  # (fTy, fCon)) = recon context names f
                                        (name :: names'' # (aTy, aCon)) = recon context names' arg in
                                        (names'' # (TyId name, (fTy, TyArr aTy (TyId name)) :: fCon ++ aCon))
recon _       names TmTrue = (names # (TyBool, []))
recon _       names TmFalse = (names # (TyBool, []))
recon context names (TmIf g t e) = let (names'   # (gTy, gCon)) = recon context names   g
                                       (names''  # (tTy, tCon)) = recon context names'  t
                                       (names''' # (eTy, eCon)) = recon context names'' e in
                                       (names''' # (tTy, (gTy, TyBool) :: (tTy, eTy) :: gCon ++ tCon ++ eCon))
recon _       names TmZero = (names # (TyNat, []))
recon context names (TmSucc x) = let (names' # (xTy, constr)) = recon context names x in
                                     (names' # (TyNat, (xTy, TyNat) :: constr))
recon context names (TmPred x) = let (names' # (xTy, constr)) = recon context names x in
                                     (names' # (TyNat, (xTy, TyNat) :: constr))
recon context names (TmIsZero x) = let (names' # (xTy, constr)) = recon context names x in
                                     (names' # (TyBool, (xTy, TyNat) :: constr))

record Substitution where
  constructor MkSub
  keys : BindingKeys
  subs : Vect (length keys) Ty

substituteHelp : (keys : BindingKeys) -> (subs : Vect (length keys) Ty) -> (var : String) -> (GetIndexData var keys) -> Ty
substituteHelp keys subs var (Left missing) = TyId var
substituteHelp keys subs var (Right (ind ** inBounds ** varIsIndex)) = index (inBoundsToFinLength ind) subs

substitute : Substitution -> String -> Ty
substitute (MkSub keys subs) var = substituteHelp keys subs var (getIndex var keys)

replace : Substitution -> Ty -> Ty
replace sub TyBool = TyBool
replace sub (TyArr x y) = TyArr (replace sub x) (replace sub y)
replace sub (TyId name) = substitute sub name
replace sub TyNat = TyNat

SubsDisjoint : Substitution -> Substitution -> Type
SubsDisjoint x y = Disjoint x.keys y.keys

appendSub : (a, b : Substitution) -> SubsDisjoint a b -> Substitution
appendSub x y disjoint = MkSub (append x.keys y.keys disjoint) (rewrite lengthAppendIsSumLength x.keys y.keys {disjoint} in x.subs ++ y.subs)

snoc : (s : Substitution) -> (key : String) -> Ty -> SetMissing key s.keys -> Substitution
snoc s key sub missingKey = MkSub (snoc s.keys key missingKey) (rewrite lengthSnocSucc s.keys key missingKey in snoc s.subs sub)

removeKeyHelp : (keys : BindingKeys) -> (subs : Vect (length keys) Ty) -> (key : String) -> (acc : (s : Substitution ** SetMissing key s.keys)) -> Disjoint (fst acc).keys keys -> (s : Substitution ** SetMissing key s.keys)
removeKeyHelp EmptySet subs key acc _ = acc
removeKeyHelp (AddElement newVal set valIsNew) (sub :: subs) key (acc ** accMissing) disjoint with (eitherNeqEq key newVal)
  removeKeyHelp (AddElement newVal set valIsNew) (sub :: subs) newVal (acc ** accMissing) (AddDisjoint accMissingNewVal accDisjointSet)| (Right Refl) = (appendSub acc (MkSub set subs) accDisjointSet ** appendMissingNew set valIsNew accDisjointSet accMissing)
  removeKeyHelp (AddElement newVal set valIsNew) (sub :: subs) key (acc ** accMissing) (AddDisjoint accMissingNewVal accDisjointSet) | (Left keyNEQnewVal) = removeKeyHelp set subs key (snoc acc newVal sub accMissingNewVal ** snocMissing key acc.keys newVal accMissing keyNEQnewVal) (snocDisjoint accDisjointSet valIsNew)

removeKey : (sub : Substitution) -> (key : String) -> (s : Substitution ** SetMissing key s.keys)
removeKey (MkSub keys subs) key = removeKeyHelp keys subs key (MkSub EmptySet [] ** EmptyMissing) (symDisjoint EmptyDisjoint)

removeKeyHelpStillMissing : (keys : BindingKeys) -> {subs : Vect (length keys) Ty} -> (key : String) -> (acc : (s : Substitution ** SetMissing key s.keys)) -> (disjoint : Disjoint (fst acc).keys keys) -> SetMissing val (appendSub acc.fst (MkSub keys subs) disjoint).keys -> SetMissing val (fst (removeKeyHelp keys subs key acc disjoint)).keys
removeKeyHelpStillMissing EmptySet key (acc ** accMissing) disjoint missing = rewrite sym $ appendEmptyRightNeutral acc.keys {disjoint} in missing
removeKeyHelpStillMissing (AddElement newVal set valIsNew) key (acc ** accMissing) {subs = sub :: subs} (AddDisjoint accMissingVal accDisjointSet) missing with (eitherNeqEq key newVal)
  removeKeyHelpStillMissing (AddElement newVal set valIsNew) newVal (acc ** accMissing) {subs = sub :: subs} (AddDisjoint accMissingVal accDisjointSet) missing | (Right Refl) =
    let (keysMissingVal, ConsMissing val newVal _ setMissingVal) = appendMissingToBothMissing (AddElement newVal set valIsNew) (AddDisjoint accMissingVal accDisjointSet) missing in
        appendMissingNew set setMissingVal accDisjointSet keysMissingVal
  removeKeyHelpStillMissing (AddElement newVal set valIsNew) key (acc ** accMissing) {subs = sub :: subs} (AddDisjoint accMissingVal accDisjointSet) missing | (Left neq) =
    removeKeyHelpStillMissing set key _ (snocDisjoint accDisjointSet valIsNew {valIsNew = accMissingVal}) missing

removeKeyStillMissing : (s : Substitution) -> (key : String) -> SetMissing val s.keys -> SetMissing val (fst (removeKey s key)).keys
removeKeyStillMissing (MkSub keys subs) key setMissing = removeKeyHelpStillMissing keys key (MkSub EmptySet [] ** EmptyMissing) (symDisjoint EmptyDisjoint) (rewrite appendEmptyLeftNeutral keys {disjoint = (symDisjoint EmptyDisjoint)} in setMissing)

withProof : (x : a) -> (y : a ** y = x)
withProof x = (x ** Refl)

mutual
  removeKeys : Substitution -> (keys : BindingKeys) -> (s : Substitution ** Disjoint s.keys keys)
  removeKeys sub EmptySet = (sub ** EmptyDisjoint)
  removeKeys sub (AddElement newVal set valIsNew) = let (sub' ** setMissing) = removeKey sub newVal
                                                        ((sub'' ** disjoint)  ** prf) = withProof (removeKeys sub' set) in
                                                        (sub'' ** AddDisjoint (rewrite (cong fst prf) in removeKeysStillMissing sub' set setMissing) disjoint)

  removeKeysStillMissing : (sub : Substitution) -> (keys : BindingKeys) -> SetMissing val (sub .keys) -> SetMissing val (((removeKeys sub keys) .fst) .keys)
  removeKeysStillMissing sub EmptySet isMissing = isMissing
  removeKeysStillMissing sub (AddElement newVal set valIsNew) isMissing with (removeKey sub newVal) proof prfRemoveKey
    removeKeysStillMissing sub (AddElement newVal set valIsNew) isMissing | (sub' ** setMissing) with (withProof (removeKeys sub' set))
      removeKeysStillMissing sub (AddElement newVal set valIsNew) isMissing | (sub' ** setMissing) | ((sub'' ** disjoint) ** prf) = rewrite (cong fst prf) in removeKeysStillMissing sub' set (rewrite sym $ cong fst prfRemoveKey in removeKeyStillMissing sub newVal isMissing)

(.) : Substitution -> Substitution -> Substitution
(.) x (MkSub keys subs) = let (keysRemoved ** disjoint) = removeKeys x keys in
                              appendSub (MkSub keys (replace x <$> subs)) keysRemoved (symDisjoint disjoint)

indexSameNatAppendSame : {keys, keys2 : BindingKeys} -> {disjoint : Disjoint keys keys2} ->
                         (ind : Nat) -> (inBounds : InBounds ind keys) -> (inBounds' : InBounds ind (append keys keys2 disjoint)) ->
                         {subs : Vect (length keys) t} -> {subs2 : Vect (length keys2) t} ->
                         index (inBoundsToFinLength ind {ok = inBounds'}) (rewrite lengthAppendIsSumLength keys keys2 {disjoint} in (subs ++ subs2)) = index (inBoundsToFinLength ind {ok = inBounds}) subs
indexSameNatAppendSame ind inBounds inBounds' {keys = EmptySet} = absurd inBounds
indexSameNatAppendSame ind inBounds inBounds' {keys = (AddElement newVal set valIsNew)} {subs = sub :: subs} with (symDisjoint disjoint)
  indexSameNatAppendSame ind inBounds inBounds' {keys = (AddElement newVal set valIsNew)} {subs = sub :: subs} | (AddDisjoint keys2MissingNewVal keys2DisjointSet) with (replace {p = (\x => InBounds ind x)} (appendConsLeftIsConsAppend set keys2 {disjoint = symDisjoint keys2DisjointSet} {valIsNewX = valIsNew} {valIsNewY = keys2MissingNewVal}) (rewrite disjointUnique (symDisjoint (AddDisjoint keys2MissingNewVal (symDisjoint (symDisjoint keys2DisjointSet)))) disjoint in inBounds'))
    indexSameNatAppendSame 0 InFirst inBounds' {keys = (AddElement newVal set valIsNew)} {subs = sub :: subs} | (AddDisjoint keys2MissingNewVal keys2DisjointSet) | InFirst = Refl
    indexSameNatAppendSame (S k) (InLater inBounds) inBounds' {keys = (AddElement newVal set valIsNew)} {subs = sub :: subs} | (AddDisjoint keys2MissingNewVal keys2DisjointSet) | (InLater inBounds'') = indexSameNatAppendSame k inBounds inBounds''

indexLenOffNatAppendSame : {keys, keys2 : BindingKeys} -> {disjoint : Disjoint keys keys2} ->
                         (ind : Nat) -> (inBounds : InBounds ind keys2) -> (inBounds' : InBounds (length keys + ind) (append keys keys2 disjoint)) ->
                         {subs : Vect (length keys) t} -> {subs2 : Vect (length keys2) t} ->
                         index (inBoundsToFinLength (length keys + ind) {ok = inBounds'}) (rewrite lengthAppendIsSumLength keys keys2 {disjoint} in (subs ++ subs2)) = index (inBoundsToFinLength ind {ok = inBounds}) subs2
indexLenOffNatAppendSame {keys = EmptySet} ind inBounds inBounds' {subs = []} =
  rewrite inBoundsUnique keys2 ind {ok = inBounds} {ok' = rewrite sym $ appendEmptyLeftNeutral keys2 {disjoint} in inBounds'} in Refl
indexLenOffNatAppendSame {keys = (AddElement newVal set valIsNew)} ind inBounds inBounds' {subs = (sub :: subs)} with (symDisjoint disjoint)
  indexLenOffNatAppendSame {keys = (AddElement newVal set valIsNew)} ind inBounds inBounds' {subs = (sub :: subs)} | (AddDisjoint keys2MissingNewVal disjoint') with (replace {p = (\x => InBounds (S (plus (length set) ind)) x)} (appendConsLeftIsConsAppend set keys2 {disjoint = symDisjoint disjoint'} {valIsNewX = valIsNew} {valIsNewY = keys2MissingNewVal}) (rewrite disjointUnique (symDisjoint (AddDisjoint keys2MissingNewVal (symDisjoint (symDisjoint disjoint')))) disjoint in inBounds'))
    indexLenOffNatAppendSame {keys = (AddElement newVal set valIsNew)} ind inBounds inBounds' {subs = (sub :: subs)} | (AddDisjoint keys2MissingNewVal disjoint') | (InLater inBounds'') = indexLenOffNatAppendSame {keys = set} ind inBounds inBounds''

indexMapIsFIndex : (vec : Vect n t) -> (f : t -> s) -> (ind : Fin n) -> (index ind (f <$> vec) = f (index ind vec))
indexMapIsFIndex (x :: _) f FZ = Refl
indexMapIsFIndex (_ :: xs) f (FS ind) = indexMapIsFIndex xs f ind

indToRemoveKeyHelpInd : (keys : BindingKeys) -> (subs : Vect (length keys) Ty) -> (key : String) -> (acc : (s : Substitution ** SetMissing key s.keys)) -> (disjoint : Disjoint (fst acc).keys keys) -> {var : String} -> (varNotKey : NEQ var key) -> (ind : Nat) -> (inBounds : InBounds ind (append (fst acc).keys keys disjoint)) -> (isInd : var = index ind (append (fst acc).keys keys disjoint)) -> (ind' : Nat ** inBounds' : InBounds ind' (fst (removeKeyHelp keys subs key acc disjoint)).keys ** var = index ind' (fst (removeKeyHelp keys subs key acc disjoint)).keys)
indToRemoveKeyHelpInd EmptySet subs key acc disjoint varNotKey ind inBounds isInd = rewrite sym $ appendEmptyRightNeutral (fst acc).keys {disjoint} in (ind ** inBounds ** isInd)
indToRemoveKeyHelpInd (AddElement newVal set valIsNew) (sub :: subs) key (acc ** accMissing) disjoint varNotKey ind inBounds isInd with (eitherNeqEq key newVal)
  indToRemoveKeyHelpInd (AddElement newVal set valIsNew) (sub :: subs) key (acc ** accMissing) (AddDisjoint accMissingNewVal accDisjointSet) varNotKey ind inBounds isInd | (Left keyNeqnewVal) = indToRemoveKeyHelpInd set subs key (snoc acc newVal sub accMissingNewVal ** snocMissing key acc.keys newVal accMissing keyNeqnewVal) (snocDisjoint accDisjointSet valIsNew) varNotKey ind inBounds isInd
  indToRemoveKeyHelpInd (AddElement newVal set valIsNew) (sub :: subs) newVal (acc ** accMissing) (AddDisjoint accMissingNewVal accDisjointSet) varNotNewVal ind inBounds isInd | (Right Refl) with (indAppendToIndEither acc.keys (AddElement newVal set valIsNew) {disjoint = (AddDisjoint accMissingNewVal accDisjointSet)} ind inBounds isInd)
    _ | (Left (inBoundsAcc ** isIndAcc)) = (ind ** indToAppendLeftInd acc.keys set ind inBoundsAcc isIndAcc)
    _ | (Right (0 ** InFirst ** varEqNewVal)) = void $ neqToNotEqual varNotNewVal varEqNewVal
    _ | (Right ((S indSet) ** (InLater inBoundsSet) ** isIndSet)) = (length acc.keys + indSet ** indToAppendRightInd acc.keys set indSet inBoundsSet isIndSet)

indToRemoveKeyInd : (sub : Substitution) -> (key : String) -> {var : String} -> (varNotKey : NEQ var key) -> (ind : Nat) -> (inBounds : InBounds ind sub.keys) -> (isInd : var = index ind sub.keys) -> (ind' : Nat ** inBounds' : InBounds ind' (fst (removeKey sub key)).keys ** var = index ind' (fst (removeKey sub key)).keys)
indToRemoveKeyInd (MkSub keys subs) key varNotKey ind inBounds isInd = indToRemoveKeyHelpInd keys subs key (MkSub EmptySet [] ** EmptyMissing) (symDisjoint EmptyDisjoint) varNotKey ind (rewrite appendEmptyLeftNeutral keys {disjoint = symDisjoint EmptyDisjoint} in inBounds) (rewrite appendEmptyLeftNeutral keys {disjoint = symDisjoint EmptyDisjoint} in isInd)

indToRemoveKeysInd : (sub : Substitution) -> (keys : BindingKeys) -> {var : String} -> (notInKeys : SetMissing var keys) -> (ind : Nat) -> (inBounds : InBounds ind sub.keys) -> (isInd : var = index ind sub.keys) -> (ind' : Nat ** inBounds' : InBounds ind' (fst (removeKeys sub keys)).keys ** var = index ind' (fst (removeKeys sub keys)).keys)
indToRemoveKeysInd sub EmptySet EmptyMissing ind inBounds isInd = (ind ** inBounds ** isInd)
indToRemoveKeysInd sub (AddElement newVal set valIsNew) (ConsMissing var newVal elemNotHead elemNotInTail) ind inBounds isInd with (removeKey sub newVal) proof removeKeyPrf
  indToRemoveKeysInd sub (AddElement newVal set valIsNew) (ConsMissing var newVal elemNotHead elemNotInTail) ind inBounds isInd | (sub' ** _) with (removeKeys sub' set) proof removeKeysPrf
    indToRemoveKeysInd sub (AddElement newVal set valIsNew) (ConsMissing var newVal elemNotHead elemNotInTail) ind inBounds isInd | (sub' ** _) | (sub'' ** _) =
      let (ind' ** inBounds' ** isInd') = replace {p = (\x => (ind' : Nat ** inBounds' : InBounds ind' x.keys ** var = index ind' x.keys))} (cong fst removeKeyPrf) $ indToRemoveKeyInd sub newVal {var} elemNotHead ind inBounds isInd in
          replace {p = (\x => (ind' : Nat ** inBounds' : InBounds ind' x.keys ** var = index ind' x.keys))} (cong DPair.fst removeKeysPrf) $ indToRemoveKeysInd sub' set {var} elemNotInTail ind' inBounds' isInd'

appendEmptyRightNeutral : {0 n : Nat} -> (vec : Vect n t) -> vec ++ [] = (rewrite plusZeroRightNeutral n in vec)
appendEmptyRightNeutral [] = Refl
appendEmptyRightNeutral (x :: xs) {n = S n} = rewrite appendEmptyRightNeutral xs in rewrite plusZeroRightNeutral n in Refl

appendConsRightIsAppendSnocLeft : {n, m : Nat} -> (a : Vect n t) -> (x : t) -> (b : Vect m t) -> a ++ (x :: b) = (rewrite sym $ plusSuccRightSucc n m in (snoc a x) ++ b)
appendConsRightIsAppendSnocLeft [] x b = Refl
appendConsRightIsAppendSnocLeft {n = S n} (y :: xs) x b = rewrite appendConsRightIsAppendSnocLeft xs x b in rewrite plusSuccRightSucc n m in Refl

inBoundsLeftAppendImpliesIndexIsOfLeftAppend : (ind : Nat) -> (keys, keys2 : BindingKeys) -> (vals : Vect (length keys) t) -> (vals2 : Vect (length keys2) t) -> {disjoint : Disjoint keys keys2} ->
                                               {inBoundsApp : InBounds ind (append keys keys2 disjoint)} -> (inBounds : InBounds ind keys) ->
                                               index (inBoundsToFinLength ind {ok = inBoundsApp}) (rewrite lengthAppendIsSumLength keys keys2 {disjoint} in vals ++ vals2) = index (inBoundsToFinLength ind {ok = inBounds}) vals
inBoundsLeftAppendImpliesIndexIsOfLeftAppend 0 (AddElement head set headIsNew) keys2 (val :: vals) vals2 InFirst with (symDisjoint disjoint)
  _ | (AddDisjoint keys2MissingHead keys2DisjointSet) with (replace {p = (\x => InBounds 0 x)} (rewrite disjointUnique disjoint (symDisjoint (AddDisjoint keys2MissingHead (symDisjoint (symDisjoint keys2DisjointSet)))) in appendConsLeftIsConsAppend set keys2 {valIsNewY = keys2MissingHead} {disjoint = symDisjoint keys2DisjointSet}) inBoundsApp)
    _ | InFirst = Refl
inBoundsLeftAppendImpliesIndexIsOfLeftAppend (S ind) (AddElement head set headIsNew) keys2 (val :: vals) vals2 (InLater inBounds) with (symDisjoint disjoint)
  _ | (AddDisjoint keys2MissingHead keys2DisjointSet) with (replace {p = (\x => InBounds (S ind) x)} (rewrite disjointUnique disjoint (symDisjoint (AddDisjoint keys2MissingHead (symDisjoint (symDisjoint keys2DisjointSet)))) in appendConsLeftIsConsAppend set keys2 {valIsNewY = keys2MissingHead} {disjoint = symDisjoint keys2DisjointSet}) inBoundsApp)
    _ | (InLater inBoundsApp') = inBoundsLeftAppendImpliesIndexIsOfLeftAppend ind set keys2 vals vals2 inBounds

inBoundsPlusLengthIpliesIndexRightAppend : (ind : Nat) -> (keys, keys2 : BindingKeys) -> (vals : Vect (length keys) t) -> (vals2 : Vect (length keys2) t) -> {disjoint : Disjoint keys keys2} ->
                                           (inBounds : InBounds (length keys + ind) (append keys keys2 disjoint)) ->
                                           (inBounds2 : InBounds ind keys2 **
                                                        index (inBoundsToFinLength (length keys + ind) {ok = inBounds}) (rewrite lengthAppendIsSumLength keys keys2 {disjoint} in vals ++ vals2)
                                                      = index (inBoundsToFinLength ind {ok = inBounds2}) vals2)
inBoundsPlusLengthIpliesIndexRightAppend ind EmptySet keys2 [] vals2 inBounds = (rewrite sym $ appendEmptyLeftNeutral keys2 in inBounds ** rewrite appendEmptyLeftNeutral keys2 {disjoint} in Refl)
inBoundsPlusLengthIpliesIndexRightAppend ind (AddElement newVal set valIsNew) keys2 (val :: vals) vals2 inBounds with (symDisjoint disjoint)
  _ | (AddDisjoint keys2MissingNewVal keys2DisjointSet) with (replace {p = (\x => InBounds (S (plus (length set) ind)) x)} (rewrite disjointUnique disjoint (symDisjoint (AddDisjoint keys2MissingNewVal (symDisjoint (symDisjoint keys2DisjointSet)))) in appendConsLeftIsConsAppend set keys2 {valIsNewY = keys2MissingNewVal} {disjoint = symDisjoint keys2DisjointSet}) inBounds)
      _ | (InLater inBounds') = inBoundsPlusLengthIpliesIndexRightAppend ind set keys2 vals vals2 inBounds'

indexSameRightAppendImpliesIndexSameRightAppend : (ind, ind2 : Nat) -> (keys, keys2 : BindingKeys) -> (vals : Vect (length keys) t) -> (vals2 : Vect (length keys2) t) -> {disjoint : Disjoint keys keys2} ->
                                                  (inBounds : InBounds ind (append keys keys2 disjoint)) -> (inBounds2 : InBounds ind2 keys2) ->
                                                  index ind (append keys keys2 disjoint) {ok = inBounds} = index ind2 keys2 {ok = inBounds2} ->
                                                  index (inBoundsToFinLength ind {ok = inBounds}) (rewrite lengthAppendIsSumLength keys keys2 {disjoint} in vals ++ vals2) = index (inBoundsToFinLength ind2 {ok = inBounds2}) vals2
indexSameRightAppendImpliesIndexSameRightAppend ind ind2 EmptySet keys2 [] vals2 inBounds inBounds2 prf = rewrite indexSameToInBoundsSame keys2 ind2 ind {ok = inBounds2} (rewrite sym prf in rewrite appendEmptyLeftNeutral keys2 {disjoint} in Refl) in rewrite appendEmptyLeftNeutral keys2 {disjoint} in Refl
indexSameRightAppendImpliesIndexSameRightAppend ind ind2 (AddElement newVal set valIsNew) keys2 (val :: vals) vals2 inBounds inBounds2 prf with (symDisjoint disjoint)
  indexSameRightAppendImpliesIndexSameRightAppend ind ind2 (AddElement newVal set valIsNew) keys2 (val :: vals) vals2 inBounds inBounds2 prf | (AddDisjoint keys2MissingNewVal keys2DisjointSet) with (replace {p = (\x => InBounds ind x)} (rewrite disjointUnique disjoint (symDisjoint (AddDisjoint keys2MissingNewVal (symDisjoint (symDisjoint keys2DisjointSet)))) in appendConsLeftIsConsAppend set keys2 {valIsNewY = keys2MissingNewVal} {disjoint = symDisjoint keys2DisjointSet}) inBounds)
    indexSameRightAppendImpliesIndexSameRightAppend 0 ind2 (AddElement newVal set valIsNew) keys2 (val :: vals) vals2 inBounds inBounds2 prf | (AddDisjoint keys2MissingNewVal keys2DisjointSet) | InFirst = void $ missingIndexAbsurd keys2 ind2 inBounds2 (trans (rewrite disjointUnique disjoint (symDisjoint (AddDisjoint keys2MissingNewVal (symDisjoint (symDisjoint keys2DisjointSet)))) in rewrite appendConsLeftIsConsAppend set keys2 {newVal} {valIsNewX = valIsNew} {valIsNewY = keys2MissingNewVal} {disjoint = (symDisjoint keys2DisjointSet)} in Refl) prf) keys2MissingNewVal
    indexSameRightAppendImpliesIndexSameRightAppend (S ind) ind2 (AddElement newVal set valIsNew) keys2 (val :: vals) vals2 inBounds inBounds2 prf | (AddDisjoint keys2MissingNewVal keys2DisjointSet) | (InLater inBounds') = indexSameRightAppendImpliesIndexSameRightAppend ind ind2 set keys2 vals vals2 inBounds' inBounds2 (trans (rewrite disjointUnique disjoint (symDisjoint (AddDisjoint keys2MissingNewVal (symDisjoint (symDisjoint keys2DisjointSet)))) in rewrite appendConsLeftIsConsAppend set keys2 {newVal} {valIsNewX = valIsNew} {valIsNewY = keys2MissingNewVal} {disjoint = (symDisjoint keys2DisjointSet)} in Refl) prf)

removeKeyHelpIndSameSub : (keys : BindingKeys) -> (subs : Vect (length keys) Ty) -> (key : String) -> (acc : (s : Substitution ** SetMissing key s.keys)) -> (disjoint : Disjoint (fst acc).keys keys) -> (keyRemoved : Substitution) ->
                          (ind : Nat) -> (inBounds : InBounds ind (append (fst acc).keys keys disjoint)) -> (ind' : Nat) -> (inBounds' : InBounds ind' (fst (removeKeyHelp keys subs key acc disjoint)).keys) ->
                          {var : String} -> {isIndex : var = index ind (append (fst acc).keys keys disjoint)} ->
                          {isIndex' : var = index ind' (fst (removeKeyHelp keys subs key acc disjoint)).keys {ok = inBounds'}} -> {varNotKey : NEQ var key} ->
                          (ind' ** inBounds' ** isIndex') = indToRemoveKeyHelpInd keys subs key acc disjoint varNotKey ind inBounds isIndex ->
                          (removedPrf : (fst (removeKeyHelp keys subs key acc disjoint) = keyRemoved)) ->
                          index (inBoundsToFinLength ind' {ok = rewrite sym removedPrf in inBounds'} {set = keyRemoved.keys}) keyRemoved.subs = index (inBoundsToFinLength ind {ok = inBounds}) (rewrite lengthAppendIsSumLength (DPair.fst acc).keys keys {disjoint} in (fst acc).subs ++ subs)
removeKeyHelpIndSameSub EmptySet [] key (acc ** _) EmptyDisjoint keyRemoved ind inBounds ind' inBounds' prf removedPrf = rewrite appendEmptyRightNeutral acc.subs in rewrite removedPrf in (cong (\x => index x keyRemoved.subs)) (indexSameToInBoundsSame keyRemoved.keys ind' ind (rewrite sym removedPrf in trans (sym isIndex') isIndex))
removeKeyHelpIndSameSub (AddElement newVal set valIsNew) (sub :: subs) key (acc ** accMissing) (AddDisjoint accMissingNewVal accDisjointSet) keyRemoved ind inBounds ind' inBounds' prf removedPrf with (eitherNeqEq key newVal)
  removeKeyHelpIndSameSub (AddElement newVal set valIsNew) (sub :: subs) key (acc ** accMissing) (AddDisjoint accMissingNewVal accDisjointSet) keyRemoved ind inBounds ind' inBounds' prf removedPrf | (Left keyNeqNewVal) =
    trans (removeKeyHelpIndSameSub set subs key (snoc acc newVal sub accMissingNewVal ** snocMissing key acc.keys newVal accMissing keyNeqNewVal) (snocDisjoint accDisjointSet valIsNew) keyRemoved ind inBounds ind' inBounds' prf removedPrf) (rewrite lengthSnocSucc acc.keys newVal accMissingNewVal in rewrite appendConsRightIsAppendSnocLeft acc.subs sub subs in Refl)
  removeKeyHelpIndSameSub (AddElement newVal set valIsNew) (sub :: subs) newVal (acc ** _) (AddDisjoint accMissingNewVal accDisjointSet) keyRemoved ind inBounds ind' inBounds' prf removedPrf | (Right Refl) with (indAppendToIndEither acc.keys (AddElement newVal set valIsNew) {disjoint = (AddDisjoint accMissingNewVal accDisjointSet)} ind inBounds isIndex)
    _ | (Left (inBoundsAcc ** isIndAcc)) =
      rewrite sym removedPrf in
      rewrite cong fst prf in
      rewrite inBoundsLeftAppendImpliesIndexIsOfLeftAppend ind acc.keys set acc.subs subs inBoundsAcc {disjoint = accDisjointSet} {inBoundsApp = rewrite cong fst (sym prf) in inBounds'} in
      rewrite inBoundsLeftAppendImpliesIndexIsOfLeftAppend ind acc.keys (AddElement newVal set valIsNew) acc.subs (sub :: subs) inBoundsAcc {disjoint = AddDisjoint accMissingNewVal accDisjointSet} {inBoundsApp = inBounds} in
              Refl
    _ | (Right (0 ** InFirst ** varEqNewVal)) = void $ neqToNotEqual varNotKey varEqNewVal
    _ | (Right ((S indSet) ** (InLater inBoundsSet) ** isIndSet)) =
      rewrite cong fst prf in
      rewrite sym removedPrf in
      let (inBounds'' ** indexSame) = (inBoundsPlusLengthIpliesIndexRightAppend indSet acc.keys set acc.subs subs (rewrite cong fst (sym prf) in inBounds')) in
          trans indexSame
                (rewrite appendConsRightIsAppendSnocLeft acc.subs sub subs in
                 rewrite sym $ lengthSnocSucc acc.keys newVal accMissingNewVal in
                 rewrite inBoundsUnique set indSet {ok = inBounds''} {ok' = inBoundsSet} in
                         sym $ indexSameRightAppendImpliesIndexSameRightAppend ind indSet (snoc acc.keys newVal accMissingNewVal) set
                                 (rewrite lengthSnocSucc acc.keys newVal accMissingNewVal in snoc acc.subs sub) subs inBounds inBoundsSet (trans (sym isIndex) isIndSet))

removeKeyIndSameSub : (sub, keyRemoved : Substitution) -> (key : String) -> (ind : Nat) -> (inBounds : InBounds ind sub.keys) -> (ind' : Nat) -> (inBounds' : InBounds ind' (fst (removeKey sub key)).keys) ->
                      {var : String} -> {isIndex : var = index ind sub.keys} -> {0 isIndex' : var = index ind' (fst (removeKey sub key)).keys} -> {varNotKey : NEQ var key} ->
                      (ind' ** inBounds' ** isIndex') = indToRemoveKeyInd sub key varNotKey ind inBounds isIndex ->
                      (removedPrf : (fst (removeKey sub key) = keyRemoved)) ->
                      index (inBoundsToFinLength ind' {ok = rewrite sym removedPrf in inBounds'} {set = keyRemoved.keys}) keyRemoved.subs = index (inBoundsToFinLength ind {ok = inBounds}) sub.subs
removeKeyIndSameSub (MkSub keys subs) keyRemoved key ind inBounds ind' inBounds' prf removedPrf = trans (removeKeyHelpIndSameSub keys subs key (MkSub EmptySet [] ** EmptyMissing) (symDisjoint EmptyDisjoint) keyRemoved ind (rewrite appendEmptyLeftNeutral keys {disjoint = symDisjoint EmptyDisjoint} in inBounds) ind' inBounds' prf removedPrf) (rewrite appendEmptyLeftNeutral keys {disjoint = symDisjoint EmptyDisjoint} in Refl)

removeKeysIndSameSub : (sub, keysRemoved : Substitution) -> (keys : BindingKeys) -> (ind : Nat) -> (inBounds : InBounds ind sub.keys) -> (ind' : Nat) -> (inBounds' : InBounds ind' (fst (removeKeys sub keys)).keys) ->
                       {var : String} -> {isIndex : var = index ind sub.keys} -> {0 isIndex' : var = index ind' (fst (removeKeys sub keys)).keys} -> {notInKeys : SetMissing var keys} ->
                       (ind' ** inBounds' ** isIndex') = indToRemoveKeysInd sub keys notInKeys ind inBounds isIndex ->
                       (removedPrf : (fst (removeKeys sub keys) = keysRemoved)) ->
                       index (inBoundsToFinLength ind' {ok = rewrite sym removedPrf in inBounds'} {set = keysRemoved.keys}) keysRemoved.subs = index (inBoundsToFinLength ind {ok = inBounds}) sub.subs
removeKeysIndSameSub sub sub EmptySet ind inBounds ind inBounds Refl Refl {notInKeys = EmptyMissing} = Refl
removeKeysIndSameSub sub keysRemoved (AddElement newVal set valIsNew) ind inBounds ind' inBounds' prf removedPrf {notInKeys = (ConsMissing var newVal elemNotHead elemNotInTail)} with (removeKey sub newVal) proof removeKeyPrf
  _ | (sub' ** _) with (removeKeys sub' set) proof removeKeysPrf
    _  | (sub'' ** _) with (replace {p = (\x => (ind' : Nat ** inBounds' : InBounds ind' x.keys ** var = index ind' x.keys))} (cong fst removeKeyPrf) $ indToRemoveKeyInd sub newVal {var} elemNotHead ind inBounds isIndex) proof indToRemovePrf
      _ | (ind'' ** inBounds'' ** isIndex'') = rewrite sym removedPrf in trans (removeKeysIndSameSub sub' sub'' set ind'' inBounds'' ind' (rewrite cong fst removeKeysPrf in inBounds') (rewrite cong fst removeKeysPrf in prf) (cong fst removeKeysPrf)) (removeKeyIndSameSub sub sub' newVal ind inBounds ind'' (rewrite cong fst removeKeyPrf in inBounds'') (rewrite cong fst removeKeyPrf in sym indToRemovePrf) (cong fst removeKeyPrf))

compProofSub : (a : Substitution) -> (b : Substitution) -> {var : String} -> substitute (a . b) var = replace a (substitute b var)
compProofSub a (MkSub keys subs) with (removeKeys a keys) proof removedPrf
  compProofSub a (MkSub keys subs) | (MkDPair keysRemoved disjoint) with (getIndex var keys)
    compProofSub a (MkSub keys subs) | (MkDPair keysRemoved disjoint) | (Right (ind ** indInBounds ** isIndex)) with (indToAppendLeftInd keys keysRemoved.keys {disjoint = symDisjoint disjoint} ind indInBounds isIndex)
      compProofSub a (MkSub keys subs) | (MkDPair keysRemoved disjoint) | (Right (ind ** indInBounds ** isIndex)) | (indInBounds' ** isIndex') = rewrite getIndexUniqueRight (append keys (keysRemoved .keys) (symDisjoint disjoint)) ind indInBounds' isIndex' in trans (indexSameNatAppendSame ind indInBounds indInBounds') (indexMapIsFIndex subs (replace a) _)
    compProofSub (MkSub keysA subsA) (MkSub keys subs) | (MkDPair keysRemoved disjoint) | (Left varNotInKeys) with (getIndex var keysA)
      compProofSub (MkSub keysA subsA) (MkSub keys subs) | (MkDPair keysRemoved disjoint) | (Left varNotInKeys) | (Right (ind ** indInBounds ** isIndex)) =
        let ((ind' ** inBounds' ** isIndex') ** removeKeysIndPrf) = withProof $ indToRemoveKeysInd (MkSub keysA subsA) keys varNotInKeys ind indInBounds isIndex
            (inBounds'' ** isIndex'') = indToAppendRightInd keys keysRemoved.keys {disjoint = symDisjoint disjoint} ind' (rewrite sym $ cong fst removedPrf in inBounds') (rewrite sym $ cong fst removedPrf in isIndex')in
            rewrite getIndexUniqueRight (append keys keysRemoved.keys (symDisjoint disjoint)) {var} (length keys + _) inBounds'' isIndex'' in
                    trans (indexLenOffNatAppendSame ind' (replace {p = (\x => InBounds ind' x.keys)} (cong fst removedPrf) inBounds') inBounds'')
                    (removeKeysIndSameSub _ _ _ ind indInBounds ind' inBounds' removeKeysIndPrf (cong fst removedPrf))
      compProofSub (MkSub keysA subsA) (MkSub keys subs) | (MkDPair keysRemoved disjoint) | (Left varNotInKeys) | (Left varNotInKeysA) =
        rewrite getIndexUniqueLeft (append keys keysRemoved.keys (symDisjoint disjoint)) {var} (appendMissingNew {x = keys} keysRemoved.keys (rewrite (sym $ cong fst removedPrf) in removeKeysStillMissing (MkSub keysA subsA) keys varNotInKeysA) (symDisjoint disjoint) varNotInKeys) in Refl

compProof : (a, b : Substitution) -> (ty: Ty) -> replace (a . b) ty = replace a (replace b ty)
compProof a b TyBool = Refl
compProof a b TyNat = Refl
compProof a b (TyArr x y) = rewrite compProof a b x in rewrite compProof a b y in Refl
compProof a b (TyId x) = compProofSub a b

emptySub : Substitution
emptySub = MkSub EmptySet []

%inline
singleSub : String -> Ty -> Substitution
singleSub key ty = MkSub (AddElement key EmptySet EmptyMissing) [ty]

replaceConstraints : Substitution -> Constr -> Constr
--replaceConstraints sub = map (\(x, y) => (replace sub x, replace sub y))
replaceConstraints sub [] = []
replaceConstraints sub ((x, y) :: xs) = (replace sub x, replace sub y) :: (replaceConstraints sub xs)

--replaceConstraints sub (MkConstr xs) = MkConstr $ map (\(x, y) => (replace sub x, replace sub y)) xs

replaceConstraintsProof : (a, b : Substitution) -> (con : Constr) -> replaceConstraints (a . b) con = replaceConstraints a (replaceConstraints b con)
replaceConstraintsProof a b [] = Refl
replaceConstraintsProof a b ((x, y) :: xs) = rewrite compProof a b x in
                                             rewrite compProof a b y in
                                             rewrite replaceConstraintsProof a b xs in
                                                     Refl

Sized Ty where
  size (TyArr x y) = S (size x + size y)
  size _ = 1

sizeTyGTE1 : (ty : Ty) -> 1 `LTE` size ty
sizeTyGTE1 (TyArr x y) = LTESucc LTEZero
sizeTyGTE1 TyBool = LTESucc LTEZero
sizeTyGTE1 (TyId x) = LTESucc LTEZero
sizeTyGTE1 TyNat = LTESucc LTEZero

size_sum : Sized t => List t -> Nat
size_sum [] = 0
size_sum (x :: xs) = size x + size_sum xs

freeVariables : Ty -> BindingKeys
freeVariables TyBool = EmptySet
freeVariables (TyArr x y) = union (freeVariables x) (freeVariables y)
freeVariables (TyId x) = AddElement x EmptySet EmptyMissing
freeVariables TyNat = EmptySet

freeVariablesConstr : Constr -> BindingKeys
freeVariablesConstr [] = EmptySet
freeVariablesConstr ((x, y) :: xs) = union (union (freeVariables x) (freeVariables y)) (freeVariablesConstr xs)

[complSize] Sized Constr where
  size = size_sum

[freeSize] Sized Constr where
  size constr = length (freeVariablesConstr constr)

data TyHasFreeVariables : Ty -> BindingKeys -> Type where
  BoolHasNoVariable : TyHasFreeVariables TyBool EmptySet
  NatHasNoVariable : TyHasFreeVariables TyNat EmptySet
  IdHasFreeVariable : TyHasFreeVariables (TyId var) (AddElement var EmptySet EmptyMissing)
  ArrowHasFreeVariables : {xVars, yVars : BindingKeys} -> TyHasFreeVariables x xVars -> TyHasFreeVariables y yVars -> TyHasFreeVariables (TyArr x y) (union xVars yVars)

tyHasFreeVariables : (ty : Ty) -> (keys : BindingKeys ** TyHasFreeVariables ty keys)
tyHasFreeVariables TyBool = (EmptySet ** BoolHasNoVariable)
tyHasFreeVariables (TyArr x y) =
  let (freeX ** prfX) = tyHasFreeVariables x
      (freeY ** prfY) = tyHasFreeVariables y in
      (union freeX freeY ** ArrowHasFreeVariables prfX prfY)
tyHasFreeVariables (TyId x) = (AddElement x EmptySet EmptyMissing ** IdHasFreeVariable)
tyHasFreeVariables TyNat = (EmptySet ** NatHasNoVariable)

tyHasVariablesSameVariables : TyHasFreeVariables ty varX -> TyHasFreeVariables ty varY -> varX = varY
tyHasVariablesSameVariables BoolHasNoVariable BoolHasNoVariable = Refl
tyHasVariablesSameVariables NatHasNoVariable NatHasNoVariable = Refl
tyHasVariablesSameVariables IdHasFreeVariable IdHasFreeVariable = Refl
tyHasVariablesSameVariables (ArrowHasFreeVariables wHasFree xHasFree) (ArrowHasFreeVariables yHasFree zHasFree) =
  rewrite tyHasVariablesSameVariables wHasFree yHasFree in
  rewrite tyHasVariablesSameVariables xHasFree zHasFree in
          Refl

data NotArrow : Ty -> Type where
  BoolNotArrow : NotArrow TyBool
  IdNotArrow : NotArrow (TyId l)
  NatNotArrow : NotArrow TyNat

Uninhabited (NotArrow (TyArr x y)) where
  uninhabited BoolNotArrow impossible
  uninhabited IdNotArrow impossible
  uninhabited NatNotArrow impossible

data NotBothArrow : (Ty, Ty) -> Type where
  LeftNotArrow : NotArrow x -> NotBothArrow (x, y)
  RightNotArrow : NotArrow y -> NotBothArrow (x, y)

Uninhabited (NotBothArrow (TyArr w y, TyArr x z)) where
  uninhabited (LeftNotArrow v) = uninhabited v
  uninhabited (RightNotArrow v) = uninhabited v

decNotBothArrow : (p : (Ty, Ty)) -> Either (w : Ty ** x : Ty ** y : Ty ** z : Ty ** p = (TyArr w x, TyArr y z)) (NotBothArrow p)
decNotBothArrow ((TyArr w x), (TyArr y z)) = Left (w ** x ** y ** z ** Refl)
decNotBothArrow (TyBool, _) = Right $ LeftNotArrow BoolNotArrow
decNotBothArrow ((TyId _), _) = Right $ LeftNotArrow IdNotArrow
decNotBothArrow (TyNat, _) = Right $ LeftNotArrow NatNotArrow
decNotBothArrow ((TyArr w x), TyBool) = Right $ RightNotArrow BoolNotArrow
decNotBothArrow ((TyArr w x), (TyId _)) = Right $ RightNotArrow IdNotArrow
decNotBothArrow ((TyArr w x), TyNat) = Right $ RightNotArrow NatNotArrow

data FreeViewArrow : Constr -> BindingKeys -> Type where
  FVAEmpty : FreeViewArrow [] EmptySet
  FVAHeadEq : {xsKeys : BindingKeys} -> FreeViewArrow xs xsKeys -> FreeViewArrow ((x, x) :: xs) xsKeys
  FVAArrow : FreeViewArrow ((w, y) :: (x, z) :: xs) keys -> Not (TyArr w x = TyArr y z) -> FreeViewArrow ((TyArr w x, TyArr y z) :: xs) keys
  FVAOther : {xKeys, yKeys, xsKeys : BindingKeys} -> TyHasFreeVariables x xKeys -> TyHasFreeVariables y yKeys -> FreeViewArrow xs xsKeys -> Not (x = y) -> NotBothArrow (x, y) ->
             FreeViewArrow ((x, y) :: xs) (union (union xKeys yKeys) xsKeys)

mutual
  mkFVAOther : (x, y : Ty) -> (xs : Constr) -> (0 acc : SizeAccessible @{Recon.complSize} ((x, y) :: xs)) -> Not (x = y) -> NotBothArrow (x, y) -> (keys : BindingKeys ** FreeViewArrow ((x, y) :: xs) keys)
  mkFVAOther x y xs (Access rec) neq notArrow =
    let (xKeys ** xPrf) = tyHasFreeVariables x
        (yKeys ** yPrf) = tyHasFreeVariables y
        (xsKeys ** xsPrf) = freeViewArrow xs (rec xs (plusLteMonotoneRight (size_sum xs) 1 (size x + size y) (transitive {rel=LTE} (sizeTyGTE1 x) (lteAddRight (size x))))) in
        (union (union xKeys yKeys) xsKeys ** FVAOther xPrf yPrf xsPrf neq notArrow)

  freeViewArrow : (constr : Constr) -> (0 acc : SizeAccessible @{Recon.complSize} constr) -> (keys : BindingKeys ** FreeViewArrow constr keys)
  freeViewArrow [] _ = (EmptySet ** FVAEmpty)
  freeViewArrow ((x, y) :: xs) acc with (decEq x y)
    freeViewArrow ((x, x) :: xs) (Access rec) | (Yes Refl) =
      let (xsVars ** xsPrf) = freeViewArrow xs (rec xs (rewrite sym $ plusOneSucc (size_sum xs) in (plusLteMonotoneRight (size_sum xs) 1 (size x + size x) (transitive {rel=LTE} (sizeTyGTE1 x) (lteAddRight (size x)))))) in
          (xsVars ** FVAHeadEq xsPrf)
    freeViewArrow ((TyArr w x, TyArr y z) :: xs) (Access rec) | (No contra) =
      let (vars ** prf) = freeViewArrow ((w, y) :: (x, z) :: xs) (rec _ (LTESucc (rewrite sym $ plusAssociative (size w) (size y) ((size x + size z) + (size_sum xs)) in rewrite sym $ plusAssociative ((size w) + (size x)) (S ((size y) + (size z))) (size_sum xs) in rewrite sym $ plusAssociative (size w) (size x) (S (((size y) + (size z)) + (size_sum xs))) in plusLteMonotoneLeft (size w) (size y + ((size x + size z) + size_sum xs)) (size x + (S (size y + size z) + size_sum xs)) (rewrite plusAssociative (size y) (size x + size z) (size_sum xs) in rewrite plusAssociative (size x) (S (size y) + size z) (size_sum xs) in plusLteMonotoneRight (size_sum xs) (size y + (size x + size z)) (size x + (S (size y) + size z)) (rewrite plusAssociative (size y) (size x) (size z) in rewrite plusAssociative (size x) (S (size y)) (size z) in rewrite plusCommutative (size x) (S (size y)) in lteSuccRight (reflexive {rel=LTE})))))) in
          (vars ** FVAArrow prf contra)
    freeViewArrow ((TyBool, y) :: xs) acc | (No contra) = mkFVAOther _ _ xs acc contra (LeftNotArrow BoolNotArrow)
    freeViewArrow (((TyId x), y) :: xs) acc | (No contra) = mkFVAOther _ _ xs acc contra (LeftNotArrow IdNotArrow)
    freeViewArrow ((TyNat, y) :: xs) acc | (No contra) = mkFVAOther _ _ xs acc contra (LeftNotArrow NatNotArrow)
    freeViewArrow (((TyArr x z), TyBool) :: xs) acc | (No contra) = mkFVAOther _ _ xs acc contra (RightNotArrow BoolNotArrow)
    freeViewArrow (((TyArr x z), (TyId y)) :: xs) acc | (No contra) = mkFVAOther _ _ xs acc contra (RightNotArrow IdNotArrow)
    freeViewArrow (((TyArr x z), TyNat) :: xs) acc | (No contra) = mkFVAOther _ _ xs acc contra (RightNotArrow NatNotArrow)

freeViewArrowSameFvaSameKeys : {xs : Constr} -> {x, y : BindingKeys} -> FreeViewArrow xs x -> FreeViewArrow xs y -> x = y
freeViewArrowSameFvaSameKeys FVAEmpty FVAEmpty = Refl
freeViewArrowSameFvaSameKeys (FVAHeadEq fvaX) (FVAHeadEq fvaY) = freeViewArrowSameFvaSameKeys fvaX fvaY
freeViewArrowSameFvaSameKeys (FVAHeadEq fvaX) (FVAArrow _ neq) = void $ neq Refl
freeViewArrowSameFvaSameKeys (FVAHeadEq fvaX) (FVAOther _ _ _ neq _) = void $ neq Refl
freeViewArrowSameFvaSameKeys (FVAArrow _ neq) (FVAHeadEq _) = void $ neq Refl
freeViewArrowSameFvaSameKeys (FVAArrow fvaX _) (FVAArrow fvaY _) = freeViewArrowSameFvaSameKeys fvaX fvaY
freeViewArrowSameFvaSameKeys (FVAArrow _ _) (FVAOther _ _ _ _ notArrows) = absurd notArrows
freeViewArrowSameFvaSameKeys (FVAOther _ _ _ neq _) (FVAHeadEq _) = void $ neq Refl
freeViewArrowSameFvaSameKeys (FVAOther _ _ _ _ notArrows) (FVAArrow _ _) = absurd notArrows
freeViewArrowSameFvaSameKeys (FVAOther xHasKeys1 yHasKeys1 fvaX _ _) (FVAOther xHasKeys2 yHasKeys2 fvaY  _ _) =
  rewrite tyHasVariablesSameVariables xHasKeys1 xHasKeys2 in
  rewrite tyHasVariablesSameVariables yHasKeys1 yHasKeys2 in
  rewrite freeViewArrowSameFvaSameKeys fvaX fvaY in
          Refl

Sized BindingKeys where
  size = length

getTailOfFVAEq : FreeViewArrow ((x, x) :: xs) keys -> FreeViewArrow xs keys
getTailOfFVAEq (FVAHeadEq y) = y
getTailOfFVAEq (FVAArrow _ neq) = void $ neq Refl
getTailOfFVAEq (FVAOther _ _ _ neq _) = void $ neq Refl

getFVAArrowOrEq : FreeViewArrow ((TyArr w x, TyArr y z) :: xs) keys -> FreeViewArrow ((w, y) :: (x, z) :: xs) keys
getFVAArrowOrEq (FVAHeadEq fvaTail) = FVAHeadEq (FVAHeadEq fvaTail)
getFVAArrowOrEq (FVAArrow fvaArrow _) = fvaArrow
getFVAArrowOrEq (FVAOther _ _ _ _ notArrows) = absurd notArrows

replaceMissingAndSub : (l : String) -> (x, tt : Ty) -> (xKeys, ttKeys, repKeys : BindingKeys) -> TyHasFreeVariables x xKeys -> TyHasFreeVariables tt ttKeys -> SetMissing l ttKeys ->
                       (TyHasFreeVariables (replace (MkSub (AddElement l EmptySet EmptyMissing) [tt]) x) repKeys) ->
                       (SetMissing l repKeys, Subset repKeys (union (union (AddElement l EmptySet EmptyMissing) ttKeys) xKeys))
replaceMissingAndSub l TyBool tt EmptySet ttKeys EmptySet BoolHasNoVariable ttHasFree ttMissingL BoolHasNoVariable = (EmptyMissing, EmptySubset)
replaceMissingAndSub l TyNat tt EmptySet ttKeys EmptySet NatHasNoVariable ttHasFree ttMissingL NatHasNoVariable = (EmptyMissing, EmptySubset)
replaceMissingAndSub l (TyId var) tt (AddElement var EmptySet EmptyMissing) ttKeys repKeys IdHasFreeVariable ttHasFree ttMissingL repHasFree with (eitherNeqEq var l)
  replaceMissingAndSub l (TyId var) tt (AddElement var EmptySet EmptyMissing) ttKeys (AddElement var EmptySet EmptyMissing) IdHasFreeVariable ttHasFree ttMissingL IdHasFreeVariable | (Left varNeqL) =
    (ConsMissing l var (symNeq varNeqL) EmptyMissing, ConsSubset (elemRightElemUnion _ _ Here) EmptySubset)
  replaceMissingAndSub l (TyId var) tt (AddElement var EmptySet EmptyMissing) ttKeys repKeys IdHasFreeVariable ttHasFree ttMissingL repHasFree | (Right varEqL) =
    rewrite tyHasVariablesSameVariables repHasFree ttHasFree in
            (ttMissingL, transitive {rel=Subset} (unionRightIsSub (AddElement l EmptySet EmptyMissing) ttKeys) (unionLeftIsSub _ _))
replaceMissingAndSub l (TyArr x y) tt (union xVars yVars) ttKeys (union xRepVars yRepVars) (ArrowHasFreeVariables xHasFree yHasFree) ttHasFree ttMissingL (ArrowHasFreeVariables xRepHasFree yRepHasFree) =
  let (xMissing, xSub) = replaceMissingAndSub l x tt xVars ttKeys xRepVars xHasFree ttHasFree ttMissingL xRepHasFree
      (yMissing, ySub) = replaceMissingAndSub l y tt yVars ttKeys yRepVars yHasFree ttHasFree ttMissingL yRepHasFree
      xSubHelp = transitive {rel=Subset} xSub (subsetRightSubsetUnion _ _ _ (unionLeftIsSub xVars yVars))
      ySubHelp = transitive {rel=Subset} ySub (subsetRightSubsetUnion _ _ _ (unionRightIsSub xVars yVars))
   in (missingBothMissingUnion _ _ xMissing yMissing, unionsSubsetSubset xRepVars _ _ xSubHelp ySubHelp)

headAndTailSub : (x, y : Ty) -> (xs : Constr) -> (xKeys, yKeys, tailKeys, allKeys : BindingKeys) -> TyHasFreeVariables x xKeys -> TyHasFreeVariables y yKeys ->
                 FreeViewArrow xs tailKeys -> FreeViewArrow ((x, y) :: xs) allKeys -> Subset allKeys (union (union xKeys yKeys) tailKeys)
headAndTailSub x x xs xKeys yKeys tailKeys allKeys xHasFree yHasFree fvaTail (FVAHeadEq fvaTail') =
  rewrite freeViewArrowSameFvaSameKeys fvaTail' fvaTail in
          unionRightIsSub _ tailKeys
headAndTailSub (TyArr w x) (TyArr y z) xs (union wVars xVars) (union yVars zVars) tailKeys allKeys (ArrowHasFreeVariables wHasFree xHasFree) (ArrowHasFreeVariables yHasFree zHasFree) fvaTail (FVAArrow fvaArrow _) =
  let (xzTail ** fvaXZ) = freeViewArrow ((x, z) :: xs) (sizeAccessible @{Recon.complSize} _)
      wySub = headAndTailSub w y ((x, z) :: xs) wVars yVars xzTail allKeys wHasFree yHasFree fvaXZ fvaArrow
      xzSub = headAndTailSub x z xs xVars zVars tailKeys xzTail xHasFree zHasFree fvaTail fvaXZ
      untangleUnionsSub1 = transitive {rel=Subset} (unionsSubsetSubset wVars yVars _ (transitive {rel=Subset} (unionLeftIsSub wVars xVars) (unionLeftIsSub _ _)) (transitive {rel=Subset} (unionLeftIsSub yVars zVars)
                                                   (unionRightIsSub _ _))) (unionLeftIsSub _ _)
      untangleUnionsSub2 = subsetLeftSubsetUnion _ _ tailKeys (unionsSubsetSubset xVars zVars _ (transitive {rel=Subset} (unionRightIsSub wVars xVars) (unionLeftIsSub _ _))
                                                                                                (transitive {rel=Subset} (unionRightIsSub yVars zVars) (unionRightIsSub _ _)))
   in transitive {rel=Subset} wySub (unionsSubsetSubset _ xzTail _ untangleUnionsSub1 (transitive {rel=Subset} xzSub untangleUnionsSub2))
headAndTailSub x y xs xKeys yKeys tailKeys (union (union xKeys yKeys) xsKeys) xHasFree yHasFree fvaTail (FVAOther xHasFree' yHasFree' fvaAll neq notArrows) =
  rewrite tyHasVariablesSameVariables xHasFree' xHasFree in
  rewrite tyHasVariablesSameVariables yHasFree' yHasFree in
  rewrite freeViewArrowSameFvaSameKeys fvaAll fvaTail in
          reflexive {rel=Subset}

replaceConstraintsSub : (l : String) -> (tt : Ty) -> (xs : Constr) -> (newFree, ttKeys, xsKeys : BindingKeys) -> TyHasFreeVariables tt ttKeys ->
                        FreeViewArrow xs xsKeys -> (FreeViewArrow (replaceConstraints (MkSub (AddElement l EmptySet EmptyMissing) [tt]) xs) newFree) ->
                        (lNotInTtKeys : SetMissing l ttKeys) ->
                        (SetMissing l newFree, Subset newFree (union (union (AddElement l EmptySet EmptyMissing) ttKeys) xsKeys))
replaceConstraintsSub l tt [] EmptySet ttKeys EmptySet ttHasKeys FVAEmpty FVAEmpty lNotInTtKeys = (EmptyMissing, EmptySubset)
replaceConstraintsSub l tt ((x, x) :: xs) newFree ttKeys xsKeys ttHasKeys (FVAHeadEq fva) fvaNew lNotInTtKeys =
  let fvaNewTail = getTailOfFVAEq fvaNew
   in replaceConstraintsSub l tt xs newFree ttKeys xsKeys ttHasKeys fva fvaNewTail lNotInTtKeys
replaceConstraintsSub l tt ((TyArr w x, TyArr y z) :: xs) newFree ttKeys xsKeys ttHasKeys (FVAArrow fva neq) fvaNew lNotInTtKeys =
  let fvaNew' = getFVAArrowOrEq fvaNew
   in replaceConstraintsSub l tt ((w, y) :: (x, z) :: xs) newFree ttKeys xsKeys ttHasKeys fva fvaNew' lNotInTtKeys
replaceConstraintsSub l tt ((x, y) :: xs) newFree ttKeys (union (union xKeys yKeys) xsKeys) ttHasKeys (FVAOther xHasKeys yHasKeys fva neq notArrows) fvaNew lNotInTtKeys =
  let (newFree' ** fvaNew') = freeViewArrow _ (sizeAccessible @{Recon.complSize} _)
      (missing', sub') = replaceConstraintsSub l tt xs newFree' ttKeys xsKeys ttHasKeys fva fvaNew' lNotInTtKeys
      (newXKeys ** newXHasFree) = tyHasFreeVariables _
      (newYKeys ** newYHasFree) = tyHasFreeVariables _
      (newXKeysMissing, newXSub) = replaceMissingAndSub l x tt xKeys ttKeys newXKeys xHasKeys ttHasKeys lNotInTtKeys newXHasFree
      (newYKeysMissing, newYSub) = replaceMissingAndSub l y tt yKeys ttKeys newYKeys yHasKeys ttHasKeys lNotInTtKeys newYHasFree
      newFreeSubUnion = headAndTailSub _ _ _ newXKeys newYKeys newFree' newFree newXHasFree newYHasFree fvaNew' fvaNew
      missing'' = missingBothMissingUnion (union newXKeys newYKeys) newFree' (missingBothMissingUnion newXKeys newYKeys newXKeysMissing newYKeysMissing) missing'
      missing = missingSetMisssingSubset missing'' newFreeSubUnion
      newXSub' = transitive {rel=Subset} newXSub (subsetRightSubsetUnion xKeys _ _ (transitive {rel=Subset} (unionLeftIsSub xKeys yKeys) (unionLeftIsSub _ xsKeys)))
      newYSub' = transitive {rel=Subset} newYSub (subsetRightSubsetUnion yKeys _ _ (transitive {rel=Subset} (unionRightIsSub xKeys yKeys) (unionLeftIsSub _ xsKeys)))
      newXYSub = unionsSubsetSubset newXKeys newYKeys _ newXSub' newYSub'
      sub''' = (transitive {rel=Subset} sub' (subsetRightSubsetUnion xsKeys _ _ (unionRightIsSub _ xsKeys)))
      sub'' = unionsSubsetSubset (union newXKeys newYKeys) newFree' _ newXYSub sub'''
      sub = transitive {rel=Subset} newFreeSubUnion sub''
   in (missing, sub)

replaceConstraintsSmaller : (l : String) -> (y : Ty) -> (xs : Constr) -> (newFree, yKeys, xsKeys : BindingKeys) -> TyHasFreeVariables y yKeys ->
                            FreeViewArrow xs xsKeys -> (FreeViewArrow (replaceConstraints (MkSub (AddElement l EmptySet EmptyMissing) [y]) xs) newFree) ->
                            (lNotInYKeys : SetMissing l yKeys) ->
                            Smaller newFree (union (union (AddElement l EmptySet EmptyMissing) yKeys) xsKeys)
replaceConstraintsSmaller l y xs newFree yKeys xsKeys yHasKeys fvaTail fvaNew lNotInYKeys =
  let (lMissing, sub) = replaceConstraintsSub l y xs newFree yKeys xsKeys yHasKeys fvaTail fvaNew lNotInYKeys
      isElem = elemLeftElemUnion _ xsKeys (elemLeftElemUnion (AddElement l EmptySet EmptyMissing) yKeys Here)
      sub2 = ConsSubset isElem sub {missing = lMissing}
   in subsetSmallerOrSameSize sub2

replaceConstraintsSmaller2 : (l : String) -> (x : Ty) -> (xs : Constr) -> (newFree, xKeys, xsKeys : BindingKeys) -> TyHasFreeVariables x xKeys ->
                            FreeViewArrow xs xsKeys -> (FreeViewArrow (replaceConstraints (MkSub (AddElement l EmptySet EmptyMissing) [x]) xs) newFree) ->
                            (lNotInXKeys : SetMissing l xKeys) ->
                            Smaller newFree (union (union xKeys (AddElement l EmptySet EmptyMissing)) xsKeys)
replaceConstraintsSmaller2 l x xs newFree xKeys xsKeys xHasKeys fvaTail fvaNew lNotInXKeys =
  let smallerOther = replaceConstraintsSmaller l x xs newFree xKeys xsKeys xHasKeys fvaTail fvaNew lNotInXKeys
      subRearanged = subsetLeftSubsetUnion _ _ xsKeys (unionSubsetSym _ xKeys)
      lteRearanged = subsetSmallerOrSameSize subRearanged
   in transitive {rel=LTE} smallerOther lteRearanged

DoesUnify : Substitution -> Constr -> Type
DoesUnify sub xs = All (uncurry (===)) (replaceConstraints sub xs)

replaceMissingNeutral : {l : String} -> {x : Ty} -> TyHasFreeVariables x keys -> SetMissing l keys -> replace (MkSub (AddElement l EmptySet EmptyMissing) [y]) x = x
replaceMissingNeutral BoolHasNoVariable _ = Refl
replaceMissingNeutral NatHasNoVariable _ = Refl
replaceMissingNeutral IdHasFreeVariable (ConsMissing l var elemNotHead _) with (eitherNeqEq var l)
  replaceMissingNeutral IdHasFreeVariable (ConsMissing l var elemNotHead _) | (Left neq') = Refl
  replaceMissingNeutral IdHasFreeVariable (ConsMissing l var elemNotHead _) | (Right eq) = void $ neqToNotEqual elemNotHead (sym eq)
replaceMissingNeutral (ArrowHasFreeVariables xHasFree yHasFree) missing =
  rewrite replaceMissingNeutral xHasFree (missingUnionMissingLeft _ _ missing) {y} in
  rewrite replaceMissingNeutral yHasFree (missingUnionMissingRight _ _ missing) {y} in
          Refl

replaceSingleIsReplaced : {l : String} -> replace (MkSub (AddElement l EmptySet EmptyMissing) [y]) (TyId l) = y
replaceSingleIsReplaced with (eitherNeqEq l l)
  replaceSingleIsReplaced | (Left neq) = void $ neqToNotEqual neq Refl
  replaceSingleIsReplaced | (Right _) = Refl

leftOrRightKeys : Either () () -> (l : String) -> (ttKeys, xsKeys : BindingKeys) -> BindingKeys
leftOrRightKeys (Left ()) l ttKeys xsKeys = union (union (AddElement l EmptySet EmptyMissing) ttKeys) xsKeys
leftOrRightKeys (Right ()) l ttKeys xsKeys = union (union ttKeys (AddElement l EmptySet EmptyMissing)) xsKeys

leftOrRightConstr : Either () () -> (l : String) -> (tt : Ty) -> (xs : Constr) -> Constr
leftOrRightConstr (Left ()) l tt xs = (TyId l, tt) :: xs
leftOrRightConstr (Right ()) l tt xs = (tt, TyId l) :: xs

replaceConstraintsSmallerBoth : (l : String) -> (tt : Ty) -> (xs : Constr) -> (newFree, ttKeys, xsKeys : BindingKeys) -> TyHasFreeVariables tt ttKeys ->
                                FreeViewArrow xs xsKeys -> (FreeViewArrow (replaceConstraints (MkSub (AddElement l EmptySet EmptyMissing) [tt]) xs) newFree) ->
                                (lNotInXKeys : SetMissing l ttKeys) -> (leftOrRight : Either () ()) ->
                                Smaller newFree (leftOrRightKeys leftOrRight l ttKeys xsKeys)
replaceConstraintsSmallerBoth l tt xs newFree ttKeys xsKeys ttHasKeys fvaTail fvaNew lNotInTtKeys (Left ()) = replaceConstraintsSmaller l tt xs newFree ttKeys xsKeys ttHasKeys fvaTail fvaNew lNotInTtKeys
replaceConstraintsSmallerBoth l tt xs newFree ttKeys xsKeys ttHasKeys fvaTail fvaNew lNotInTtKeys (Right ()) = replaceConstraintsSmaller2 l tt xs newFree ttKeys xsKeys ttHasKeys fvaTail fvaNew lNotInTtKeys

makeUnifyLeftOrRight : (leftOrRight : Either () ()) -> (sub : Substitution) -> replace sub (TyId l) = replace sub tt -> DoesUnify sub xs -> DoesUnify sub (leftOrRightConstr leftOrRight l tt xs)
makeUnifyLeftOrRight (Left ()) sub headSame doesUnifyTail = headSame :: doesUnifyTail
makeUnifyLeftOrRight (Right ()) sub headSame doesUnifyTail = (sym headSame) :: doesUnifyTail

mutual
  uthelp : (l : String) -> (ttKeys, xsKeys : BindingKeys) -> (leftOrRight : Either () ()) -> (0 accFree : SizeAccessible (leftOrRightKeys leftOrRight l ttKeys xsKeys)) ->
            (tt : Ty) -> (xs : Constr) -> (ttHasFree : TyHasFreeVariables tt ttKeys) -> (fvaTail : FreeViewArrow xs xsKeys) -> GetIndexData l ttKeys ->
            Maybe (sub : Substitution ** DoesUnify sub (leftOrRightConstr leftOrRight l tt xs))
            --Maybe (sub : Substitution ** DoesUnify sub ((TyId l, tt) :: xs))
  uthelp l ttKeys xsKeys leftOrRight (Access rec) tt xs ttHasFree fvaTail (Left lNotInTtKeys) = do
    let (newTail ** newTailPrf) = withProof (replaceConstraints (singleSub l tt) xs)
    let (newTailVars ** vfaNewTail) = freeViewArrow newTail (sizeAccessible @{Recon.complSize} newTail)
    let newSmaller = replaceConstraintsSmallerBoth l tt xs newTailVars ttKeys xsKeys ttHasFree fvaTail (rewrite sym newTailPrf in vfaNewTail) lNotInTtKeys leftOrRight
    (subs ** doesUnify) <- unify_total newTailVars (rec newTailVars newSmaller) newTail vfaNewTail
    let headSame = rewrite compProof subs (singleSub l tt) tt in
                   rewrite compProof subs (singleSub l tt) (TyId l) in
                   rewrite replaceMissingNeutral ttHasFree lNotInTtKeys {y=tt} in
                   rewrite replaceSingleIsReplaced {l} {y=tt} in
                           Refl
    let doesUnify' = rewrite replaceConstraintsProof subs (singleSub l tt) xs in
                     rewrite sym newTailPrf in
                             doesUnify
    let newDoesUnify = makeUnifyLeftOrRight leftOrRight (subs . (singleSub l tt)) headSame doesUnify' {l} {tt} {xs}
    Just (subs . (singleSub l tt) ** newDoesUnify)
  uthelp l ttKeys xsKeys leftOrRight accFree tt xs ttHasFree fvaTail (Right _) = Nothing

  unify_total : (freeVariables : BindingKeys) -> (0 accFree : SizeAccessible freeVariables) -> (constr : Constr) -> (FreeViewArrow constr freeVariables) -> Maybe (sub : Substitution ** DoesUnify sub constr)
  unify_total EmptySet accFree [] FVAEmpty = Just (emptySub ** [])
  unify_total freeVariables accFree ((x, x) :: xs) (FVAHeadEq fvaTail) = do (sub ** doesUnify) <- unify_total freeVariables accFree xs fvaTail
                                                                            Just (sub ** Refl :: doesUnify)
  unify_total freeVariables accFree ((TyArr w x, TyArr y z) :: xs) (FVAArrow fvaArrow neq) = do (sub ** rwEQry :: rxEQrz :: doesUnify) <- unify_total freeVariables accFree _ fvaArrow
                                                                                                Just (sub ** rewrite rwEQry in rewrite rxEQrz in Refl :: doesUnify)
  unify_total (union (union (AddElement l EmptySet EmptyMissing) yKeys) xsKeys) accFree (((TyId l), y) :: xs) (FVAOther IdHasFreeVariable yHasFree fvaTail neq notArrows) =
    uthelp l yKeys xsKeys (Left ()) accFree y xs yHasFree fvaTail (getIndex l yKeys)
  unify_total (union (union xKeys (AddElement l EmptySet EmptyMissing)) xsKeys) accFree ((x, (TyId l)) :: xs) (FVAOther xHasFree IdHasFreeVariable fvaTail neq notArrows) =
    uthelp l xKeys xsKeys (Right ()) accFree x xs xHasFree fvaTail (getIndex l xKeys)
  unify_total (union (union xKeys yKeys) xsKeys) accFree ((_, _) :: xs) (FVAOther xHasFree yHasFree fvaTail neq notArrows) = Nothing

unify : (constr : Constr) -> Maybe (sub : Substitution ** DoesUnify sub constr)
unify xs = let (freeVariables ** freeViewArrow) = freeViewArrow xs (sizeAccessible @{Recon.complSize} xs)
            in unify_total freeVariables (sizeAccessible freeVariables) xs freeViewArrow

getPrincipal : Term 0 -> Maybe Ty
getPrincipal term = do let (_ # (ty, constr)) = recon [] names term
                       (unifier ** _) <- unify constr
                       Just (replace unifier ty)

repContext : Substitution -> Context n -> Context n
repContext _ [] = []
repContext sub ((nm, ty) :: xs) = (nm, replace sub ty) :: repContext sub xs

repTerm : Substitution -> Term n -> Term n
repTerm sub (TmAbs nm ty body) = TmAbs nm (replace sub ty) (repTerm sub body)
repTerm sub (TmApp f arg) = TmApp (repTerm sub f) (repTerm sub arg)
repTerm sub (TmIf g t e) = TmIf (repTerm sub g) (repTerm sub t) (repTerm sub e)
repTerm sub (TmSucc x) = TmSucc (repTerm sub x)
repTerm sub (TmPred x) = TmPred (repTerm sub x)
repTerm sub (TmIsZero x) = TmIsZero (repTerm sub x)
repTerm sub (TmVar l) = TmVar l
repTerm sub TmTrue = TmTrue
repTerm sub TmFalse = TmFalse
repTerm sub TmZero = TmZero

namespace RecM
  data RecRes : Type -> Type where
    MkRecRes : (result : a) -> (1 x : HLStream String) -> RecRes a
    RecResFail : (1 x : HLStream String) -> RecRes a

  PrimRecM : Type -> Type
  PrimRecM a = (1 x : HLStream String) -> RecRes a

  export
  data RecM : Type -> Type where
    MkRecM : (1 fn : PrimRecM a) -> RecM a

  Functor RecM where
    map f (MkRecM fn) = MkRecM (\names => case fn names of
                                               MkRecRes res names' => MkRecRes (f res) names'
                                               RecResFail names' => RecResFail names')

  export
  Applicative RecM where
    (<*>) (MkRecM fnFn) (MkRecM fnVal) = MkRecM (\names => case fnFn names of
                                                                MkRecRes f names' => case fnVal names' of
                                                                                          MkRecRes val names'' => MkRecRes (f val) names''
                                                                                          RecResFail names'' => RecResFail names''
                                                                RecResFail names' => RecResFail names')

    pure result = MkRecM (MkRecRes result)

  export
  Monad RecM where
    (>>=) (MkRecM fnA) f = MkRecM (\names => case fnA names of
                                                  MkRecRes aa names' => let (MkRecM fnB) = f aa
                                                                         in fnB names'
                                                  RecResFail names' => RecResFail names')

  prim_getName : PrimRecM String
  prim_getName (name :: names) = MkRecRes name names

  export
  getName : RecM String
  getName = MkRecM prim_getName

  export
  runRecM : HLStream String -> RecM a -> Maybe a
  runRecM names (MkRecM fn) = case fn names of
                                   MkRecRes result _ => Just result
                                   RecResFail _ => Nothing

  prim_fail : PrimRecM a
  prim_fail names = RecResFail names

  fail : RecM a
  fail = MkRecM prim_fail

  export
  lift : Maybe a -> RecM a
  lift Nothing = fail
  lift (Just val) = pure val

--assert_totals in here are because I'm too lazy to put in a well-Founded proof, and I think it's trivial that repTerm does not affect the term size
incrRecon : Context n -> Term n -> RecM (Substitution, Ty)
incrRecon context (TmVar x) = pure (emptySub, snd (index x context))
incrRecon context (TmAbs nm ty body) = do (sub, bTy) <- incrRecon ((nm, ty) :: context) body
                                          pure (sub, TyArr (replace sub ty) bTy)
incrRecon context (TmApp f arg) = do (fSub, fTy) <- incrRecon context f
                                     let fContext = repContext fSub context
                                     let subbedArg = repTerm fSub arg
                                     (aSub, aTy) <- assert_total $ incrRecon fContext subbedArg
                                     name <- getName
                                     (conSub ** _) <- lift $ unify [(fTy, TyArr aTy (TyId name))]
                                     pure (conSub . aSub. fSub, replace conSub (TyId name))
incrRecon context TmTrue = pure (emptySub, TyBool)
incrRecon context TmFalse = pure (emptySub, TyBool)
incrRecon context (TmIf g t e) = do (gSub, gTy) <- incrRecon context g
                                    (gBoolSub ** _) <- lift $ unify [(gTy, TyBool)]
                                    let gContext = repContext (gBoolSub . gSub) context
                                    let subbedT = repTerm (gBoolSub. gSub) t
                                    (tSub, tTy) <- assert_total $ incrRecon gContext subbedT
                                    let tContext = repContext tSub gContext
                                    let subbedE = repTerm (tSub . gBoolSub . gSub) e
                                    (eSub, eTy) <- assert_total $ incrRecon tContext subbedE
                                    let tTy' = replace eSub tTy
                                    (teSub ** _) <- lift $ unify [(tTy', eTy)]
                                    pure (teSub . eSub . tSub . gBoolSub . gSub, replace teSub eTy)
incrRecon context TmZero = pure (emptySub, TyNat)
incrRecon context (TmSucc x) = do (xSub, ty) <- incrRecon context x
                                  (isNatSub ** _) <- lift $ unify [(ty, TyNat)]
                                  pure (isNatSub . xSub, TyNat)
incrRecon context (TmPred x) = do (xSub, ty) <- incrRecon context x
                                  (isNatSub ** _) <- lift $ unify [(ty, TyNat)]
                                  pure (isNatSub . xSub, TyNat)
incrRecon context (TmIsZero x) = do (xSub, ty) <- incrRecon context x
                                    (isNatSub ** _) <- lift $ unify [(ty, TyNat)]
                                    pure (isNatSub . xSub, TyBool)

runIncrRecon : Term 0 -> Maybe Ty
runIncrRecon term = snd <$> runRecM names (incrRecon [] term)
