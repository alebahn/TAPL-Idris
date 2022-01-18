module Ty

import Data.Fun
import Data.Fin
import Data.Fin.Order
import Data.Nat
import Data.Rel
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality
import Decidable.Decidable

%default total

public export
data Ty : Nat -> Type where
  TyVar : (k : Fin n) -> Ty n
  TyArr : Ty n -> Ty n -> Ty n
  TyAll : Ty (S n) -> Ty n
  TySome : Ty (S n) -> Ty n

maybeEq : (x, y : Ty n) -> Maybe (x = y)
maybeEq (TyVar x) (TyVar y) with (decEq x y)
  maybeEq (TyVar x) (TyVar x) | (Yes Refl) = Just Refl
  maybeEq (TyVar x) (TyVar y) | (No contra) = Nothing
maybeEq (TyArr w x) (TyArr y z) with (maybeEq w y)
  maybeEq (TyArr w x) (TyArr y z) | Nothing = Nothing
  maybeEq (TyArr w x) (TyArr w z) | (Just Refl) with (maybeEq x z)
    maybeEq (TyArr w x) (TyArr w z) | (Just Refl) | Nothing = Nothing
    maybeEq (TyArr w x) (TyArr w x) | (Just Refl) | (Just Refl) = Just Refl
maybeEq (TyAll x) (TyAll y) with (maybeEq x y)
  maybeEq (TyAll x) (TyAll y) | Nothing = Nothing
  maybeEq (TyAll x) (TyAll x) | (Just Refl) = Just Refl
maybeEq (TySome x) (TySome y) with (maybeEq x y)
  maybeEq (TySome x) (TySome y) | Nothing = Nothing
  maybeEq (TySome x) (TySome x) | (Just Refl) = Just Refl
maybeEq _ _ = Nothing

maybeEqEqIsJust : (x : Ty n) -> IsJust (maybeEq x x)
maybeEqEqIsJust (TyVar x) with (decEq x x)
  maybeEqEqIsJust (TyVar x) | (Yes Refl) = ItIsJust
  maybeEqEqIsJust (TyVar x) | (No contra) = void $ contra Refl
maybeEqEqIsJust (TyArr x y) with (maybeEq x x) proof xPrf
  maybeEqEqIsJust (TyArr x y) | Nothing = absurd $ the (IsJust (Nothing {ty = (x = x)})) (rewrite sym xPrf in maybeEqEqIsJust x)
  maybeEqEqIsJust (TyArr x y) | (Just Refl) with (maybeEq y y) proof yPrf
    maybeEqEqIsJust (TyArr x y) | (Just Refl) | Nothing = absurd $ the (IsJust (Nothing {ty = (y = y)})) (rewrite sym yPrf in maybeEqEqIsJust y)
    maybeEqEqIsJust (TyArr x y) | (Just Refl) | (Just Refl) = ItIsJust
maybeEqEqIsJust (TyAll x)  with (maybeEq x x) proof prf
  maybeEqEqIsJust (TyAll x) | Nothing = absurd $ the (IsJust (Nothing {ty = (x = x)})) (rewrite sym prf in maybeEqEqIsJust x)
  maybeEqEqIsJust (TyAll x) | (Just Refl) = ItIsJust
maybeEqEqIsJust (TySome x) with (maybeEq x x) proof prf
  maybeEqEqIsJust (TySome x) | Nothing = absurd $ the (IsJust (Nothing {ty = (x = x)})) (rewrite sym prf in maybeEqEqIsJust x)
  maybeEqEqIsJust (TySome x) | (Just Refl) = ItIsJust

public export
DecEq (Ty n) where
  decEq t u with (maybeEq t u) proof prf
    decEq t u | Nothing = No (\(Refl {x}) => uninhabited $ the (IsJust (Nothing {ty = (x = x)})) (rewrite sym prf in maybeEqEqIsJust x))
    decEq t u | (Just eq) = Yes eq

data TyNaming : Ty n -> Type where
  VarUnamed : TyNaming (TyVar v)
  ArrNaming : TyNaming x -> TyNaming y -> TyNaming (TyArr x y)
  AllName : String -> TyNaming body -> TyNaming (TyAll body)
  SomeName : String -> TyNaming body -> TyNaming (TySome body)

shiftUp : Ty n -> (offset : Nat) -> (c : Fin (offset + n)) -> Ty (offset + n)
shiftUp (TyVar k) offset c with (decide c (rewrite plusCommutative offset n in weakenN offset k) {k=2} {ts=[Fin (offset + n), Fin (offset + n)]} {p=FinLTE})
  shiftUp (TyVar k) offset c | (Yes prf) = TyVar (shift offset k)
  shiftUp (TyVar k) offset c | (No contra) = TyVar (rewrite plusCommutative offset n in weakenN offset k)
shiftUp (TyArr x y) offset c = TyArr (shiftUp x offset c) (shiftUp y offset c)
shiftUp (TyAll x) offset c = TyAll (rewrite plusSuccRightSucc offset n in (shiftUp x offset (rewrite sym $ plusSuccRightSucc offset n in FS c)))
shiftUp (TySome x) offset c = TySome (rewrite plusSuccRightSucc offset n in (shiftUp x offset (rewrite sym $ plusSuccRightSucc offset n in FS c)))

export
shiftUpBase : Ty n -> (offset : Nat) -> Ty (offset + n)
shiftUpBase ty 0 = ty
shiftUpBase ty (S k) = shiftUp ty (S k) FZ

{-
data CanShiftDown : (offset : Nat) -> (c : Fin (offset + n)) -> Ty (offset + n) -> Type where
  VarCanShiftDown : (k : Fin (offset + n)) -> (c : Fin (offset + n)) -> Either (LT (finToNat k) (finToNat c)) (LTE (finToNat c + offset) (finToNat k)) -> CanShiftDown offset {n} c (TyVar k)
  ArrCanShiftDown : CanShiftDown offset {n} c fTy -> CanShiftDown offset {n} c aTy -> CanShiftDown offset {n} c (TyArr fTy aTy)
  AllCanShiftDown : {0 offset, n : Nat} -> {0 c : Fin (offset + n)} -> {0 bTy : Ty (S offset + n)} -> CanShiftDown offset {n = S n} (rewrite sym $ plusSuccRightSucc offset n in FS c) (rewrite sym $ plusSuccRightSucc offset n in bTy) -> CanShiftDown offset {n} c (TyAll bTy)
  SomeCanShiftDown : {0 offset, n : Nat} -> {0 c : Fin (offset + n)} -> {0 bTy : Ty (S offset + n)} -> CanShiftDown offset {n = S n} (rewrite sym $ plusSuccRightSucc offset n in FS c) (rewrite sym $ plusSuccRightSucc offset n in bTy) -> CanShiftDown offset {n} c (TySome bTy)
  -}

export
data CanShiftDown : (c : Fin (S n)) -> Ty (S n) -> Type where
  VarCanShiftDown : (k : Fin (S n)) -> (c : Fin (S n)) -> Not (c = k) -> CanShiftDown c (TyVar k)
  ArrCanShiftDown : CanShiftDown c fTy -> CanShiftDown c aTy -> CanShiftDown c (TyArr fTy aTy)
  AllCanShiftDown : CanShiftDown (FS c) bTy -> CanShiftDown c (TyAll bTy)
  SomeCanShiftDown : CanShiftDown (FS c) bTy -> CanShiftDown c (TySome bTy)

Uninhabited (CanShiftDown c (TyVar c)) where
  uninhabited (VarCanShiftDown  c c contra) = contra Refl

export
canShiftDown : (c : Fin (S n)) -> (ty : Ty (S n)) -> Dec (CanShiftDown c ty)
canShiftDown c (TyVar k) with (decEq c k)
  canShiftDown c (TyVar c) | (Yes Refl) = No uninhabited
  canShiftDown c (TyVar k) | (No contra) = Yes (VarCanShiftDown k c contra)
canShiftDown c (TyArr x y) with (canShiftDown c x)
  canShiftDown c (TyArr x y) | (Yes xPrf) with (canShiftDown c y)
    canShiftDown c (TyArr x y) | (Yes xPrf) | (Yes yPrf) = Yes (ArrCanShiftDown xPrf yPrf)
    canShiftDown c (TyArr x y) | (Yes xPrf) | (No contra) = No (\(ArrCanShiftDown _ yPrf) => contra yPrf)
  canShiftDown c (TyArr x y) | (No contra) = No (\(ArrCanShiftDown xPrf _) => contra xPrf)
canShiftDown c (TyAll bTy) with (canShiftDown (FS c) bTy)
  canShiftDown c (TyAll bTy) | (Yes prf) = Yes (AllCanShiftDown prf)
  canShiftDown c (TyAll bTy) | (No contra) = No (\(AllCanShiftDown prf) => contra prf)
canShiftDown c (TySome bTy) with (canShiftDown (FS c) bTy)
  canShiftDown c (TySome bTy) | (Yes prf) = Yes (SomeCanShiftDown prf)
  canShiftDown c (TySome bTy) | (No contra) = No (\(SomeCanShiftDown prf) => contra prf)

strengthenVar : (c : Fin (S n)) -> (k : Fin (S n)) -> (FinLTE c k -> Void) -> Fin n
strengthenVar FZ k f = void $ f (FromNatPrf LTEZero)
strengthenVar (FS FZ) FZ f = FZ
strengthenVar (FS FZ) (FS k) f = void $ f (FromNatPrf (LTESucc LTEZero))
strengthenVar (FS (FS c)) FZ f = FZ
strengthenVar (FS (FS c)) (FS k) f = FS (strengthenVar (FS c) k (\(FromNatPrf prf) => f (FromNatPrf $ LTESucc prf)))

shiftDownVar : (c, k : Fin (S n)) -> FinLTE c k -> (c = k -> Void) -> Fin n
shiftDownVar FZ FZ lte neq = void $ neq Refl
shiftDownVar FZ (FS k) lte neq = k
shiftDownVar (FS c) FZ (FromNatPrf lte) neq = absurd lte
shiftDownVar (FS c) (FS FZ) lte neq = FZ
shiftDownVar (FS c) (FS (FS k)) (FromNatPrf (LTESucc lte)) neq = FS $ shiftDownVar c (FS k) (FromNatPrf lte) (neq . (cong FS))

export
shiftDown : (ty : Ty (S n)) -> (c : Fin (S n)) -> CanShiftDown c ty -> Ty n
shiftDown (TyVar k) c (VarCanShiftDown k c f) with (decide c k {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftDown (TyVar k) c (VarCanShiftDown k c f) | (Yes prf) = TyVar (shiftDownVar c k prf f)
  shiftDown (TyVar k) c (VarCanShiftDown k c f) | (No contra) = TyVar (strengthenVar c k contra)
shiftDown (TyArr fTy aTy) c (ArrCanShiftDown x y) = TyArr (shiftDown aTy c y) (shiftDown aTy c y)
shiftDown (TyAll bTy) c (AllCanShiftDown x) = TyAll (shiftDown bTy (FS c) x)
shiftDown (TySome bTy) c (SomeCanShiftDown x) = TySome (shiftDown bTy (FS c) x)

finToNatWeakenNEQ : {0 n : Nat} -> (j : Nat) -> (k : Fin n) -> finToNat {n = j + n} (rewrite plusCommutative j n in weakenN j k) = finToNat k
finToNatWeakenNEQ j FZ = Refl
finToNatWeakenNEQ j (FS k) = cong S (finToNatWeakenNEQ j k)

lteToSuccNE : {0 n : Nat} -> {k : Fin n} -> {c : Fin (S n)} -> FinLTE c (rewrite plusCommutative 1 n in weakenN 1 k) -> c = FS k -> Void
lteToSuccNE (FromNatPrf lte) prf = (LTEImpliesNotGT lte) (rewrite finToNatWeakenNEQ 1 k in rewrite cong finToNat prf in reflexive {rel=LTE})

notLTEToNotEq : {0 n : Nat} -> {c : Fin (S n)} -> (k : Fin n) -> (FinLTE c (rewrite plusCommutative 1 n in weakenN 1 k) -> Void) -> c = (rewrite plusCommutative 1 n in weakenN 1 k) -> Void
notLTEToNotEq k notLTE prf = notLTE (rewrite prf in reflexive {rel=FinLTE})

shiftUpCanShiftDown : (ty : Ty n) -> (c : Fin (S n)) -> CanShiftDown c (shiftUp ty 1 c)
shiftUpCanShiftDown (TyVar k) c with (decide c (rewrite plusCommutative 1 n in weakenN 1 k) {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftUpCanShiftDown (TyVar k) c | (Yes prf) = VarCanShiftDown (FS k) c (lteToSuccNE prf)
  shiftUpCanShiftDown (TyVar k) c | (No contra) = VarCanShiftDown (rewrite plusCommutative 1 n in weakenN 1 k) c (notLTEToNotEq k contra)
shiftUpCanShiftDown (TyArr x y) c = ArrCanShiftDown (shiftUpCanShiftDown x c) (shiftUpCanShiftDown y c)
shiftUpCanShiftDown (TyAll x) c = AllCanShiftDown (shiftUpCanShiftDown x (FS c))
shiftUpCanShiftDown (TySome x) c = SomeCanShiftDown (shiftUpCanShiftDown x (FS c))

substitute : (var : Fin (S n)) -> (replacement : Ty (S n)) -> CanShiftDown var replacement -> (body : Ty (S n)) -> (ty : Ty (S n) ** CanShiftDown var ty)
substitute var replacement repCanShift (TyVar k) with (decEq var k)
  substitute var replacement repCanShift (TyVar k) | (Yes prf) = (replacement ** repCanShift)
  substitute var replacement repCanShift (TyVar k) | (No contra) = (TyVar k ** VarCanShiftDown k var contra)
substitute var replacement repCanShift (TyArr x y) = let (xSub ** xCanShift) = substitute var replacement repCanShift x
                                                         (ySub ** yCanShift) = substitute var replacement repCanShift y
                                                      in (TyArr xSub ySub ** ArrCanShiftDown xCanShift yCanShift)
substitute var replacement repCanShift (TyAll x) = let (xSub ** xCanShift) = substitute (FS var) (shiftUp replacement 1 (FS var)) (shiftUpCanShiftDown replacement (FS var)) x
                                                    in (TyAll xSub ** AllCanShiftDown xCanShift)
substitute var replacement repCanShift (TySome x) = let (xSub ** xCanShift) = substitute (FS var) (shiftUp replacement 1 (FS var)) (shiftUpCanShiftDown replacement (FS var)) x
                                                    in (TySome xSub ** SomeCanShiftDown xCanShift)

export
substituteFirst : (replacement : Ty n) -> (body : Ty (S n)) -> Ty n
substituteFirst replacement body = let (newBody ** canShift) = substitute FZ (shiftUp replacement 1 FZ) (shiftUpCanShiftDown replacement FZ) body
                                    in shiftDown newBody FZ canShift

public export
countDown : (n : Nat) -> Vect n Nat
countDown 0 = []
countDown (S k) = k :: countDown k

public export
Tys : Nat -> Type
Tys k = All Ty (countDown k)

substituteMany : {m, n : Nat} -> (replacements : Tys n) -> (body : Ty (m + n)) -> Ty m
substituteMany [] body = rewrite sym $ plusZeroRightNeutral m in  body
substituteMany (ty :: tys) body {n = S n} = let (newBody ** canShift) = substitute (weakenN {m = S m} n last) (shiftUp ty (S m) last) ?body ?cnsh
                                                newBody' = shiftDown newBody (weakenN {m = S m} n last) canShift
                                             in substituteMany tys newBody'
