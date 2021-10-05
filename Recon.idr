module Recon

import Data.DPair
import Data.Fin
import Data.Vect
import Data.Vect.Elem
import Data.Stream
import Data.List.Elem
import Decidable.Equality

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

freeVariables : Ty -> List String
freeVariables TyBool = []
freeVariables (TyArr x y) = freeVariables x ++ freeVariables y
freeVariables (TyId x) = [x]
freeVariables TyNat = []

record Substitution where
  constructor MkSub
  keys : BindingKeys
  subs : Vect (length keys) Ty

substituteHelp : (keys : BindingKeys) -> (subs : Vect (length keys) Ty) -> (var : String) -> (IndexData var keys) -> Ty
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

removeKeyHelp' : (keys : BindingKeys) -> (subs : Vect (length keys) Ty) -> (key : String) -> (acc : (s : Substitution ** SetMissing key s.keys)) -> Disjoint keys (fst acc).keys -> (s : Substitution ** SetMissing key s.keys)
removeKeyHelp' EmptySet subs key acc _ = acc
removeKeyHelp' (AddElement newVal set valIsNew) (sub :: subs) key (acc ** accMissing) disjoint with (eitherNeqEq key newVal)
  removeKeyHelp' (AddElement newVal set valIsNew) (sub :: subs) newVal (acc ** accMissing) (AddDisjoint accMissingNewVal setDisjointAcc) | (Right Refl) = (appendSub (MkSub set subs) acc setDisjointAcc ** appendMissingNew set valIsNew setDisjointAcc accMissingNewVal)
  removeKeyHelp' (AddElement newVal set valIsNew) (sub :: subs) key (acc ** accMissing) (AddDisjoint accMissingNewVal setDisjointAcc) | (Left keyNEQnewVal) = removeKeyHelp' set subs key (snoc acc newVal sub accMissingNewVal ** snocMissing key acc.keys newVal accMissing keyNEQnewVal) (snocDisjoint setDisjointAcc valIsNew)

removeKey' : (sub : Substitution) -> (key : String) -> (s : Substitution ** SetMissing key s.keys)
removeKey' (MkSub keys subs) key = removeKeyHelp' keys subs key (MkSub EmptySet [] ** EmptyMissing) (symDisjoint EmptyDisjoint)

mutual
  removeKeyHelp : (keys : BindingKeys) -> (subs : Vect (length keys) Ty) -> (key : String) -> (s : Substitution ** SetMissing key s.keys)
  removeKeyHelp EmptySet subs key = (MkSub EmptySet [] ** EmptyMissing)
  removeKeyHelp (AddElement newVal set valIsNew) (sub :: subs) key with (eitherNeqEq key newVal)
    removeKeyHelp (AddElement newVal set valIsNew) (sub :: subs) newVal | (Right Refl) = (MkSub set subs ** valIsNew)
    removeKeyHelp (AddElement newVal set valIsNew) (sub :: subs) key | (Left neq) with (removeKeyHelp set subs key) proof prf
      removeKeyHelp (AddElement newVal set valIsNew) (sub :: subs) key | (Left neq) | ((MkSub set' subs') ** removedMissing) =
        (MkSub (AddElement newVal set' (rewrite sym $ cong (.keys) $ cong fst prf in removeKeyHelpStillMissing set key valIsNew)) (sub :: subs') ** ConsMissing key newVal neq removedMissing)

  removeKeyHelpStillMissing : (keys : BindingKeys) -> {subs : Vect (length keys) Ty} -> (key : String) -> SetMissing val keys -> SetMissing val (fst (removeKeyHelp keys subs key)).keys
  removeKeyHelpStillMissing EmptySet key isMissing = isMissing
  removeKeyHelpStillMissing (AddElement newVal set valIsNew) key (ConsMissing val newVal headMissing elemNotInTail) {subs = a :: b} with (eitherNeqEq key newVal)
    removeKeyHelpStillMissing (AddElement newVal set valIsNew) newVal (ConsMissing val newVal headMissing elemNotInTail) {subs = a :: b} | (Right Refl) = elemNotInTail
    removeKeyHelpStillMissing (AddElement newVal set valIsNew) key (ConsMissing val newVal headMissing elemNotInTail) {subs = a :: b} | (Left neq) with (removeKeyHelp set b key) proof prf
      removeKeyHelpStillMissing (AddElement newVal set valIsNew) key (ConsMissing val newVal headMissing elemNotInTail) | (Left neq) | ((MkSub set' subs') ** removedMissing) =
        ConsMissing val newVal headMissing (rewrite sym $ cong (.keys) $ cong fst prf in removeKeyHelpStillMissing set key elemNotInTail)

removeKeyHelpStillMissingInv : (keys : BindingKeys) -> {val : String} -> {subs : Vect (length keys) Ty} -> (key : String) -> NEQ val key -> SetMissing val (fst (removeKeyHelp keys subs key)).keys -> SetMissing val keys
removeKeyHelpStillMissingInv EmptySet key neq missing = missing
removeKeyHelpStillMissingInv (AddElement newVal set valIsNew) key neq missing {subs = a :: b} with (eitherNeqEq key newVal)
  removeKeyHelpStillMissingInv (AddElement newVal set valIsNew) newVal neq missing {subs = a :: b} | (Right Refl) = (ConsMissing val newVal neq missing)
  removeKeyHelpStillMissingInv (AddElement newVal set valIsNew) key neq missing {subs = a :: b} | (Left neq') with (removeKeyHelp set b key) proof prf
    removeKeyHelpStillMissingInv (AddElement newVal set valIsNew) key neq (ConsMissing val newVal elemNotHead elemNotInTail) {subs = a :: b} | (Left neq') | (MkSub set' subs' ** removedMissing) =
      ConsMissing val newVal elemNotHead (removeKeyHelpStillMissingInv set key neq {subs = b} (rewrite prf in elemNotInTail))

removeKey : Substitution -> (key : String) -> (s : Substitution ** SetMissing key s.keys)
removeKey (MkSub keys subs) = removeKeyHelp keys subs

removeKeyStillMissing : (s : Substitution) -> (key : String) -> SetMissing val s.keys -> SetMissing val (fst (removeKey s key)).keys
removeKeyStillMissing (MkSub keys subs) = removeKeyHelpStillMissing keys

withProof : (x : a) -> (y : a ** y = x)
withProof x = (x ** Refl)

mutual
  removeKeys : Substitution -> (keys : BindingKeys) -> (s : Substitution ** Disjoint keys s.keys)
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
(.) x (MkSub keys subs) = uncurry (appendSub (MkSub keys (replace x <$> subs))) (removeKeys x keys)

subAppendMissingFistSecond : (fstSub, sndSub : Substitution) -> (disjoint : Disjoint fstSub.keys sndSub.keys) -> (var : String) -> SetMissing var fstSub.keys -> substitute (appendSub fstSub sndSub disjoint) var = substitute sndSub var

--setMissingToIndexNeq : {name : String} -> {names : BindingKeys} -> (nameIsNew : SetMissing name names) -> (i : Nat) -> {0 ok : InBounds i names} -> NEQ name (index i names)
--neqToNotEqual : NEQ a b -> Not (a = b)

subConsEqSub : {var, newVal : String} -> {set : BindingKeys} -> {0 valIsNew : _} -> {0 subs : _} -> NEQ var newVal -> substitute (MkSub (AddElement newVal set valIsNew) (sub :: subs)) var = substitute (MkSub set subs) var
subConsEqSub neq with (eitherNeqEq var newVal)
  subConsEqSub neq | (Right eqPrf) = void $ neqToNotEqual neq eqPrf
  subConsEqSub neq | (Left neq') with (getIndex var set)
    subConsEqSub neq | (Left neq') | (Left _) = Refl
    subConsEqSub neq | (Left neq') | (Right (ind ** inBounds ** isIndex)) = Refl

consSub : (key : String) -> (sub : Ty) -> (tail : Substitution) -> {isNew : SetMissing key (tail.keys)} -> Substitution
consSub key sub (MkSub keys subs) = MkSub (AddElement key keys isNew) (sub :: subs)

subRemoveKeyHelpMissingUnchanged : {var : String} -> (keys : BindingKeys) -> (subs : Vect (length keys) Ty) -> (key : String) -> NEQ var key -> substitute ((removeKeyHelp keys subs key) .fst) var = substitute (MkSub keys subs) var
subRemoveKeyHelpMissingUnchanged EmptySet [] key neq = Refl
subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq with (eitherNeqEq key newVal)
  subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) newVal neq | (Right Refl) = sym $ subConsEqSub neq
  subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left keyNeqNewVal) with (removeKeyHelp set subs key) proof prf
    subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left keyNeqNewVal) | (MkSub keys' subs' ** removedMissing) with (eitherNeqEq var newVal) proof eitherNeqEqVarNewValPrf
      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left keyNeqNewVal) | (MkSub keys' subs' ** removedMissing) | (Left varNeqNewVal) =
        ?subRemoveKeyHelpMissingUnchanged_rhs_4
        --rewrite (sym $ cong (.keys) $ cong fst prf) in ?subRemoveKeyHelpMissingUnchanged_rhs_4
        --trans (replace  eitherNeqEqVarNewValPrf (subConsEqSub varNeqNewVal) {p = (\x => substituteHelp (AddElement newVal keys' (removeKeyHelpStillMissing set key valIsNew)) (sub :: subs') var (case x of {Right eqPrf => Right (0 ** InFirst ** eqPrf); Left neq => case (getIndex var keys') of {Left tailMissing => Left (ConsMissing var newVal neq tailMissing); Right (n ** inBounds ** isIndex) => Right (MkDPair (S n) (MkDPair (InLater inBounds) isIndex))}}) = substituteHelp keys' subs' var (getIndex var keys'))}) ?subRemoveKeyHelpMissingUnchanged_rhs_4
      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left keyNeqNewVal) | (MkSub keys' subs' ** removedMissing) | (Right varEqNewVal) = Refl

{-
--subRemoveKeyHelpMissingUnchanged EmptySet [] key neq = Refl
--subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq with (eitherNeqEq key newVal)
--  subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) with (getIndex var (AddElement newVal set valIsNew))
--    subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Left missing) with (getIndex var set)
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Left missing) | (Left _) = Refl
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Left (ConsMissing var newVal elemNotHead elemNotInTail)) | (Right (ind ** _ ** isIndex)) =
--        void $ neqToNotEqual (setMissingToIndexNeq elemNotInTail ind) isIndex
--    subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Right (ind ** inBounds ** isIndex)) with (getIndex var set)
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Right (ind ** inBounds ** isIndex)) | (Left missing) =
--        void $ neqToNotEqual (setMissingToIndexNeq (ConsMissing var newVal (rewrite sym eqPrf in neq) missing) ind) isIndex
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Right (ind ** inBounds ** isIndex)) | (Right (ind' ** inBounds' ** isIndex')) =
--        case inBounds of
--             InFirst => void $ neqToNotEqual neq (trans isIndex (sym eqPrf))
--             (InLater x {k}) => rewrite indexSameToInBoundsSame set ind' k (trans (sym isIndex') isIndex) {ok = inBounds'} {ok' = x} in Refl
--  subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') with (removeKeyHelp set subs key) proof prf
--    subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) with (eitherNeqEq var newVal) proof eqNeqPrf
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') with (getIndex var set)
--        subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') | (Left setMissingVar) with (getIndex var keys')
--          subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') | (Left setMissingVar) | (Left keys'MissingVar) =
--            Refl
--          subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') | (Left setMissingVar) | (Right (ind ** inBounds ** isIndex)) =
--            void $ neqToNotEqual (setMissingToIndexNeq (replace {p = SetMissing var} (cong (.keys) $ cong fst prf) (removeKeyHelpStillMissing set key {subs} setMissingVar)) ind) isIndex
--        subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') | (Right (ind ** inBounds ** isIndex)) =
--          rewrite sym $ cong (.keys) $ cong fst prf in ?subRemoveKeyHelpMissingUnchanged_rhs_4 (sym $ subRemoveKeyHelpMissingUnchanged set subs key neq)
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Right eq) = Refl
      
--subRemoveKeyHelpMissingUnchanged EmptySet [] key neq = Refl
--subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq with (eitherNeqEq key newVal)
--  subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) with (getIndex var (AddElement newVal set valIsNew))
--    subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Left missing) with (getIndex var set)
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Left missing) | (Left _) = Refl
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Left (ConsMissing var newVal elemNotHead elemNotInTail)) | (Right (ind ** _ ** isIndex)) =
--        void $ neqToNotEqual (setMissingToIndexNeq elemNotInTail ind) isIndex
--    subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Right (ind ** inBounds ** isIndex)) with (getIndex var set)
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Right (ind ** inBounds ** isIndex)) | (Left missing) =
--        void $ neqToNotEqual (setMissingToIndexNeq (ConsMissing var newVal (rewrite sym eqPrf in neq) missing) ind) isIndex
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Right eqPrf) | (Right (ind ** inBounds ** isIndex)) | (Right (ind' ** inBounds' ** isIndex')) =
--        case inBounds of
--             InFirst => void $ neqToNotEqual neq (trans isIndex (sym eqPrf))
--             (InLater x {k}) => rewrite indexSameToInBoundsSame set ind' k (trans (sym isIndex') isIndex) {ok = inBounds'} {ok' = x} in Refl
--  subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') with (removeKeyHelp set subs key) proof prf
--    subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) with (eitherNeqEq var newVal)
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') with (getIndex var keys') proof prfIndexKeys'
--        subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') | (Left keys'MissingVar) with (getIndex var set)
--          subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') | (Left keys'MissingVar) | (Left setMissingVar) = Refl
--          subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') | (Left keys'MissingVar) | (Right (ind ** inBounds ** isIndex)) =
--            void $ neqToNotEqual (setMissingToIndexNeq (removeKeyHelpStillMissingInv set key neq {subs} (rewrite prf in keys'MissingVar)) ind) isIndex
--        subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') | (Right (ind ** inBounds ** isIndex)) with (getIndex var set) proof prfIndexSet
--          subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') | (Right (ind ** inBounds ** isIndex)) | (Left setMissingVar) =
--            void $ neqToNotEqual (setMissingToIndexNeq (replace {p = SetMissing var} (cong (.keys) $ cong fst prf) (removeKeyHelpStillMissing set key {subs} setMissingVar)) ind) isIndex
--          subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Left neq'') | (Right (ind ** inBounds ** isIndex)) | (Right (ind' ** inBounds' ** isIndex')) =
--            ?subRemoveKeyHelpMissingUnchanged_rhs_2 (subRemoveKeyHelpMissingUnchanged set subs key neq)
--      subRemoveKeyHelpMissingUnchanged (AddElement newVal set valIsNew) (sub :: subs) key neq | (Left neq') | ((MkSub keys' subs') ** removedMissing) | (Right eq) = Refl
-}

subRemoveKeyMissingUnchanged : {var : String} -> {sub : Substitution} -> (key : String) -> NEQ var key -> substitute ((removeKey sub key) .fst) var = substitute sub var
subRemoveKeyMissingUnchanged {sub = (MkSub keys subs)} key neq = subRemoveKeyHelpMissingUnchanged keys subs key neq

subRemoveKeysMissingUnchanged : {sub : Substitution} -> (keys : BindingKeys) -> SetMissing var keys -> substitute ((removeKeys sub keys) .fst) var = substitute sub var
subRemoveKeysMissingUnchanged EmptySet missing = Refl
subRemoveKeysMissingUnchanged (AddElement newVal set valIsNew) (ConsMissing var newVal elemNotHead elemNotInTail) with (removeKey sub newVal) proof prfRemoveKey
  subRemoveKeysMissingUnchanged (AddElement newVal set valIsNew) (ConsMissing var newVal elemNotHead elemNotInTail) | (sub' ** setMissing) with (withProof (removeKeys sub' set))
    subRemoveKeysMissingUnchanged (AddElement newVal set valIsNew) (ConsMissing var newVal elemNotHead elemNotInTail) | (sub' ** setMissing) | ((sub'' ** disjoint) ** prf) =
      rewrite (cong fst prf) in rewrite sym $ cong fst prfRemoveKey in trans (subRemoveKeysMissingUnchanged set elemNotInTail) (subRemoveKeyMissingUnchanged newVal elemNotHead)

compProofSub : (a : Substitution) -> (b : Substitution) -> {var : String} -> substitute (a . b) var = replace a (substitute b var)
--compProofSub a (MkSub keys subs) with (getIndex var keys)
--  compProofSub a (MkSub keys subs) | (Right (ind ** inBounds ** varIsIndex)) = ?compProofSub_rhs_2
--  compProofSub a (MkSub keys subs) | (Left missing) = trans (subAppendMissingFistSecond _ ((removeKeys a keys).fst) ((removeKeys a keys).snd) var missing) (subRemoveKeysMissingUnchanged keys missing)
--  --compProofSub a (MkSub keys subs) | (Left missing) with (removeKeys a keys) proof prf
--  --  compProofSub a (MkSub keys subs) | (Left missing) | (removed ** disjoint) = ?compProofSub_rhs

compProof : (a, b : Substitution) -> (ty: Ty) -> replace (a . b) ty = replace a (replace b ty)
compProof a b TyBool = Refl
compProof a b TyNat = Refl
compProof a b (TyArr x y) = rewrite compProof a b x in rewrite compProof a b y in Refl
compProof a b (TyId x) = compProofSub a b

unify : Constr -> Maybe Substitution

{-
record Substitution where
  constructor MkSub
  0 size : Nat
  keys : Vect size String
  subs : Vect size Ty

emptySub : Substitution
emptySub = MkSub 0 [] []

singleSub : String -> Ty -> Substitution
singleSub key sub = MkSub 1 [key] [sub]

consSub : String -> Ty -> Substitution -> Substitution
consSub key sub (MkSub size keys subs) = MkSub (S size) (key :: keys) (sub :: subs)

appendSub : Substitution -> Substitution -> Substitution
appendSub (MkSub size keys subs) (MkSub size2 keys2 subs2) = MkSub (size + size2) (keys ++ keys2) (subs ++ subs2)

KeyInSub : String -> Substitution -> Type
KeyInSub search (MkSub size keys subs) = Elem search keys

keyInSub : (search : String) -> (sub : Substitution) -> Dec (KeyInSub search sub)
keyInSub search (MkSub size keys subs) = isElem search keys

removeAllInstancesHelp : String -> Vect size String -> Vect size Ty -> Substitution
removeAllInstancesHelp search [] [] = emptySub
removeAllInstancesHelp search (key :: keys) (sub :: subs) with (decEq search key)
  removeAllInstancesHelp search (key :: keys) (sub :: subs) | (Yes prf) = removeAllInstancesHelp search keys subs
  removeAllInstancesHelp search (key :: keys) (sub :: subs) | (No contra) = consSub key sub (removeAllInstancesHelp search keys subs)

removeAllInstances : String -> Substitution -> Substitution
removeAllInstances search (MkSub size keys subs) = removeAllInstancesHelp search keys subs

substitute : Substitution -> String -> Ty
substitute (MkSub size keys subs) name with (isElem name keys)
  substitute (MkSub size keys subs) name | (Yes prf) = index (elemToFin prf) subs
  substitute (MkSub size keys subs) name | (No contra) = TyId name

subSub : Substitution -> (0 size2 : Nat) -> Vect size2 String -> Vect size2 Ty -> Substitution
subSub x 0 [] [] = emptySub
subSub x (S len) (key :: keys) (sub :: subs) = consSub key (replace x sub) (subSub x len keys subs)

removeKeys : Substitution -> Vect k String -> Substitution
removeKeys sub [] = sub
removeKeys sub (key :: keys) = removeKeys (removeAllInstances key sub) keys

(.) : Substitution -> Substitution -> Substitution
(.) x (MkSub size keys subs) = appendSub (subSub x size keys subs) (removeKeys x keys)

elemRemoveIsElemWhole : (s : Substitution) -> (key : String) -> (keys : Vect len String) -> KeyInSub key (removeKeys s keys) -> KeyInSub key s
elemRemoveIsElemWhole s key [] x = x
elemRemoveIsElemWhole s key (y :: xs) x = ?elemRemoveIsElemWhole_rhs_2 --(elemRemoveIsElemWhole (removeAllInstances y s) key xs x)
--KeyInSub key (removeKeys (removeAllInstances y s) xs)

elemToNotElemRemoveKeys : (s : Substitution) -> (keys : Vect k String) -> (key : String) -> Elem key keys -> Not (KeyInSub key (removeKeys s keys))
elemToNotElemRemoveKeys s (_ :: xs) key Here elemSub with (keyInSub key s)
  elemToNotElemRemoveKeys s (_ :: xs) key Here elemSub | (Yes prf) = ?elemToNotElemRemoveKeys_rhs_1
  elemToNotElemRemoveKeys s (_ :: xs) key Here elemSub | (No contra) = ?elemToNotElemRemoveKeys_rhs_3 --contra (elemRemoveIsElemWhole s key xs elemSub)
elemToNotElemRemoveKeys s (y :: xs) key (There later) elemSub = ?elemToNotElemRemoveKeys_rhs_2

--subSubElem : (s : Substitution) -> (0 size2 : Nat) -> (keys : Vect size2 String) -> (subs : Vect size2 Ty) -> (key : String) -> (elem : Elem key keys) -> subSub s size2 keys subs = replace s (elemToFin elem)

elemIsElemSubSub : (s : Substitution) -> (0 size2 : Nat) -> (keys : Vect size2 String) -> (subs : Vect size2 Ty) -> (key : String) -> Elem key keys -> KeyInSub key (subSub s size2 keys subs)
elemIsElemSubSub s (S len) (_ :: xs) (sub :: subs) key Here = conSubHere key (replace s sub) _
  where
    conSubHere : (key : String) -> (sub : Ty) -> (s : Substitution) -> KeyInSub key (consSub key sub s)
    conSubHere key sub (MkSub size keys subs) = Here
elemIsElemSubSub s (S len) (y :: xs) (sub :: subs) key (There later) = conSubThere y (replace s sub) _ (elemIsElemSubSub s len xs subs key later)
  where
    conSubThere : (key : String) -> (sub : Ty) -> (s : Substitution) -> KeyInSub key2 s -> KeyInSub key2 (consSub key sub s)
    conSubThere key sub (MkSub size keys subs) x = There x

appendElem : (a : Vect n t) -> (b : Vect m t) -> Elem key a -> Elem key (a ++ b)
appendElem (key :: xs) b Here = Here
appendElem (y :: xs) b (There later) = There (appendElem xs b later)

inSubIsInAppend : (a, b : Substitution) -> KeyInSub key a -> KeyInSub key (appendSub a b)
inSubIsInAppend (MkSub size keys subs) (MkSub size2 keys2 subs2) elem = appendElem keys keys2 elem

--substitute : Substitution -> String -> Ty
substituteElem : (s : Substitution) -> (var : String) -> (elem : Elem var s.keys) -> (substitute s var) = index (elemToFin elem) s.subs
substituteElem (MkSub size keys subs) var elem with (isElem var keys)
  substituteElem (MkSub size keys subs) var elem | (Yes prf) = ?substituteElem_rhs_1
  substituteElem (MkSub size keys subs) var elem | (No contra) = ?substituteElem_rhs_2

subsProof : (a, k : Substitution) -> (ty : Ty) -> replace (a . k) ty = replace a (replace k ty)
subsProof a _ TyBool = Refl
subsProof a _ TyNat = Refl
subsProof a b (TyArr x y) = rewrite subsProof a b x in rewrite subsProof a b y in Refl
subsProof a (MkSub size keys subs) (TyId x) with (isElem x keys)
  subsProof a (MkSub size keys subs) (TyId x) | (Yes prf) = ?subsProof_rhs_1 (inSubIsInAppend (subSub a size keys subs) (removeKeys a keys) (elemIsElemSubSub a size keys subs x prf))
  subsProof a (MkSub size keys subs) (TyId x) | (No contra) = ?subsProof_rhs_2


unify : Constr -> Maybe Substitution
unify [] = Just emptySub
unify ((x, y) :: xs) with (decEq x y)
  unify ((x, x) :: xs) | (Yes Refl) = unify xs
  unify ((x, y) :: xs) | (No _) with (x)
    unify ((x, y) :: xs) | (No _) | (TyId l) with (isElem l (freeVariables y))
      unify ((x, y) :: xs) | (No _) | (TyId l) | (Yes prf) = Nothing
      unify ((x, y) :: xs) | (No _) | (TyId l) | (No contra) = do
        subs <- ?unify_rhs_5
        Just (consSub l y subs)
    unify ((x, y) :: xs) | (No _) | (TyArr z w) = ?unify_rhs_2
    unify ((x, y) :: xs) | (No _) | TyBool = ?unify_rhs_1
    unify ((x, y) :: xs) | (No _) | TyNat = ?unify_rhs_4
    -}
