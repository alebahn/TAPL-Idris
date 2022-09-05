module Ty

import Data.DPair
import Data.Fun
import Data.Fin
import Data.Fin.Order
import Data.Nat
import Data.Rel
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality
import Decidable.Decidable
import Control.Function

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

export
shiftUp : {n : _} -> Ty n -> (offset : Nat) -> (c : Fin (offset + n)) -> Ty (offset + n)
shiftUp (TyVar k) offset c with (decide c (coerce (plusCommutative n offset) (weakenN offset k)) {k=2} {ts=[Fin (offset + n), Fin (offset + n)]} {p=FinLTE})
  shiftUp (TyVar k) offset c | (Yes prf) = TyVar (shift offset k)
  shiftUp (TyVar k) offset c | (No contra) = TyVar (coerce (plusCommutative n offset) (weakenN offset k))
shiftUp (TyArr x y) offset c = TyArr (shiftUp x offset c) (shiftUp y offset c)
shiftUp (TyAll x) offset c = TyAll (rewrite plusSuccRightSucc offset n in (shiftUp x offset (rewrite sym $ plusSuccRightSucc offset n in FS c)))
shiftUp (TySome x) offset c = TySome (rewrite plusSuccRightSucc offset n in (shiftUp x offset (rewrite sym $ plusSuccRightSucc offset n in FS c)))

export
shiftUpBase : {n : _} -> Ty n -> (offset : Nat) -> Ty (offset + n)
shiftUpBase ty 0 = ty
shiftUpBase ty (S k) = shiftUp ty (S k) FZ

public export
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

public export
shiftDown : (ty : Ty (S n)) -> (c : Fin (S n)) -> CanShiftDown c ty -> Ty n
shiftDown (TyVar k) c (VarCanShiftDown k c f) with (decide c k {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftDown (TyVar k) c (VarCanShiftDown k c f) | (Yes prf) = TyVar (shiftDownVar c k prf f)
  shiftDown (TyVar k) c (VarCanShiftDown k c f) | (No contra) = TyVar (strengthenVar c k contra)
shiftDown (TyArr fTy aTy) c (ArrCanShiftDown x y) = TyArr (shiftDown fTy c x) (shiftDown aTy c y)
shiftDown (TyAll bTy) c (AllCanShiftDown x) = TyAll (shiftDown bTy (FS c) x)
shiftDown (TySome bTy) c (SomeCanShiftDown x) = TySome (shiftDown bTy (FS c) x)

lteToSuccNE : {0 n : Nat} -> {k : Fin n} -> {c : Fin (S n)} -> FinLTE c (coerce (plusCommutative n 1) (weakenN 1 k)) -> c = FS k -> Void
lteToSuccNE (FromNatPrf lte) prf = (LTEImpliesNotGT lte) (rewrite prf in LTESucc $ rewrite finToNatQuotient (transitive (coerceEq (plusCommutative n 1)) (weakenNNeutral 1 k)) in reflexive)

notLTEToNotEq : {n : Nat} -> {c : Fin (S n)} -> (k : Fin n) -> (FinLTE c (coerce (plusCommutative n 1) (weakenN 1 k)) -> Void) -> c = (coerce (plusCommutative n 1) (weakenN 1 k)) -> Void
notLTEToNotEq k notLTE prf = notLTE (rewrite prf in reflexive)

export
shiftUpCanShiftDown : {n : _} -> (ty : Ty n) -> (c : Fin (S n)) -> CanShiftDown c (shiftUp ty 1 c)
shiftUpCanShiftDown (TyVar k) c with (decide c (coerce (plusCommutative n 1) (weakenN 1 k)) {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftUpCanShiftDown (TyVar k) c | (Yes prf) = VarCanShiftDown (FS k) c (lteToSuccNE prf)
  shiftUpCanShiftDown (TyVar k) c | (No contra) = VarCanShiftDown (coerce (plusCommutative n 1) (weakenN 1 k)) c (notLTEToNotEq k contra)
shiftUpCanShiftDown (TyArr x y) c = ArrCanShiftDown (shiftUpCanShiftDown x c) (shiftUpCanShiftDown y c)
shiftUpCanShiftDown (TyAll x) c = AllCanShiftDown (shiftUpCanShiftDown x (FS c))
shiftUpCanShiftDown (TySome x) c = SomeCanShiftDown (shiftUpCanShiftDown x (FS c))

export
shiftUpBaseCanShiftDown : {n : _} -> (ty : Ty n) -> CanShiftDown FZ (shiftUpBase ty 1)
shiftUpBaseCanShiftDown ty = shiftUpCanShiftDown ty FZ

shiftDownVarSameIsSame : {c, k : Fin (S n)} -> (lte : FinLTE c k) -> (f, g : (c = k -> Void)) -> shiftDownVar c k lte f = shiftDownVar c k lte g
shiftDownVarSameIsSame {c = FZ} {k = FZ} _ neq _ = void $ neq Refl
shiftDownVarSameIsSame {c = FZ} {k = (FS k)} _ _ _ = Refl
shiftDownVarSameIsSame {c = (FS c)} {k = FZ} (FromNatPrf lte) _ _ = absurd lte
shiftDownVarSameIsSame {c = (FS c)} {k = (FS FZ)} _ _ _ = Refl
shiftDownVarSameIsSame {c = (FS c)} {k = (FS (FS k))} (FromNatPrf (LTESucc lte)) f g = cong FS $ shiftDownVarSameIsSame (FromNatPrf lte) (f . (cong FS)) (g . (cong FS))

export
shiftDownSameIsSame : (ty : Ty (S n)) -> (c : Fin (S n)) -> (csA, csB : CanShiftDown c ty) -> shiftDown ty c csA = shiftDown ty c csB
shiftDownSameIsSame (TyVar k) c (VarCanShiftDown k c f) (VarCanShiftDown k c g) with (decide c k {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftDownSameIsSame (TyVar k) c (VarCanShiftDown k c f) (VarCanShiftDown k c g) | (Yes prf) = cong TyVar $ shiftDownVarSameIsSame prf f g
  shiftDownSameIsSame (TyVar k) c (VarCanShiftDown k c f) (VarCanShiftDown k c g) | (No contra) = Refl
shiftDownSameIsSame (TyArr fTy aTy) c (ArrCanShiftDown x y) (ArrCanShiftDown z w) = rewrite shiftDownSameIsSame fTy c x z in rewrite shiftDownSameIsSame aTy c y w in Refl
shiftDownSameIsSame (TyAll bTy) c (AllCanShiftDown x) (AllCanShiftDown y) = cong TyAll $ shiftDownSameIsSame bTy (FS c) x y
shiftDownSameIsSame (TySome bTy) c (SomeCanShiftDown x) (SomeCanShiftDown y) = cong TySome $ shiftDownSameIsSame bTy (FS c) x y

shiftDownVarFSIsId : (var : Fin (S n)) -> (k : Fin n) -> (prf : FinLTE var (FS k)) -> (f : (var = FS k -> Void)) -> shiftDownVar var (FS k) prf f = k
shiftDownVarFSIsId FZ k lte neq = Refl
shiftDownVarFSIsId (FS c) FZ lte neq = Refl
shiftDownVarFSIsId (FS c) (FS k) (FromNatPrf (LTESucc lte)) neq = cong FS (shiftDownVarFSIsId c k (FromNatPrf lte) (neq . (cong FS)))

strengthenVarWeakenNIsId : {n : Nat} -> (k : Fin n) -> (var : Fin (S n)) -> {eq : (n + 1) = (1 + n)} -> (contra : (FinLTE var (coerce eq (weakenN 1 k)) -> Void)) ->
                           (strengthenVar {n=n} var (coerce eq (weakenN 1 k)) contra) = k
strengthenVarWeakenNIsId k FZ contra = void $ contra $ FromNatPrf LTEZero
strengthenVarWeakenNIsId FZ (FS FZ) contra = Refl
strengthenVarWeakenNIsId FZ (FS (FS var)) contra = Refl
strengthenVarWeakenNIsId (FS k) (FS FZ) contra = void $ contra $ FromNatPrf $ LTESucc $ LTEZero
strengthenVarWeakenNIsId (FS k) (FS (FS var)) contra = cong FS $ (strengthenVarWeakenNIsId k (FS var) _)

shiftDownShiftUpIsId : {n : _} -> (var : Fin (S n)) -> (ty : Ty n) -> (tyCanShiftDown : CanShiftDown var (shiftUp ty 1 var)) -> (shiftDown (shiftUp ty 1 var) var tyCanShiftDown) = ty
shiftDownShiftUpIsId var (TyVar k) tyCanShiftDown with (decide var (coerce (plusCommutative n 1) (weakenN 1 k)) {k=2} {ts=[Fin (1 + n), Fin (1 + n)]} {p=FinLTE})
  shiftDownShiftUpIsId var (TyVar k) (VarCanShiftDown _ var f) | (Yes prf) with (decide var (FS k) {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
    shiftDownShiftUpIsId var (TyVar k) (VarCanShiftDown _ var f) | (Yes prf) | (Yes prf2) = cong TyVar $ shiftDownVarFSIsId var k prf2 f
    shiftDownShiftUpIsId var (TyVar k) (VarCanShiftDown _ var f) | (Yes (FromNatPrf prf)) | (No contra) =
      void $ contra $ FromNatPrf $ lteSuccRight $ rewrite sym $ finToNatQuotient (transitive (coerceEq (plusCommutative n 1)) (weakenNNeutral 1 k)) in prf
  shiftDownShiftUpIsId var (TyVar k) (VarCanShiftDown _ var f) | (No contra) with (decide var (coerce (plusCommutative n 1) (weakenN 1 k)) {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
    shiftDownShiftUpIsId var (TyVar k) (VarCanShiftDown _ var f) | (No contra) | (Yes prf) = void $ contra prf
    shiftDownShiftUpIsId var (TyVar k) (VarCanShiftDown _ var f) | (No contra) | (No contra2) = cong TyVar $ strengthenVarWeakenNIsId k var contra2
shiftDownShiftUpIsId var (TyArr x y) (ArrCanShiftDown xCanShift yCanShift) = rewrite shiftDownShiftUpIsId var x xCanShift in rewrite shiftDownShiftUpIsId var y yCanShift in Refl
shiftDownShiftUpIsId var (TyAll ty) (AllCanShiftDown canShift) = cong TyAll (shiftDownShiftUpIsId (FS var) ty canShift)
shiftDownShiftUpIsId var (TySome ty) (SomeCanShiftDown canShift) = cong TySome (shiftDownShiftUpIsId (FS var) ty canShift)

--shiftDownShiftUpBaseToShiftUpBaseShiftDown : {n : _} -> (var : Fin (S n)) -> (ty : Ty (S n)) -> (tyCanShiftDown : CanShiftDown (FS var) (shiftUpBase ty 1)) -> (shiftDown (shiftUpBase ty 1) (FS var) tyCanShiftDown) = (shiftUpBase (shiftDown ty var ?csd) 1)

--shiftDownShiftUpToShiftUpShiftDown : {n : _} -> (varUp : Fin (S n)) -> (varDown : Fin n) -> (FinLTE varUp (weaken varDown)) -> (ty : Ty (S n)) -> (tyCanShiftDown : CanShiftDown (FS varDown) (shiftUp ty 1 varUp)) -> (shiftDown (shiftUp ty 1 varUp) (FS varDown) tyCanShiftDown) = (shiftUp (shiftDown ty varDown ?csd) 1 varUp)

strengthenVarNeutral : (c : Fin (S n)) -> (k : Fin (S n)) -> {0 contra : Not (FinLTE c k)} -> strengthenVar c k contra ~~~ k
strengthenVarNeutral FZ k = void $ contra (FromNatPrf LTEZero)
strengthenVarNeutral (FS FZ) FZ = FZ
strengthenVarNeutral (FS FZ) (FS k) = void $ contra (FromNatPrf (LTESucc LTEZero))
strengthenVarNeutral (FS (FS c)) FZ = FZ
strengthenVarNeutral (FS (FS c)) (FS k) = FS $ strengthenVarNeutral (FS c) k

strengthenVarAndFSCommute : (c, k : Fin (S n)) -> {0 contra : Not (FinLTE (FS c) (FS k))} -> {0 contra2 : Not (FinLTE c k)} -> strengthenVar (FS c) (FS k) contra = FS (strengthenVar c k contra2)
strengthenVarAndFSCommute FZ k = void $ contra2 $ FromNatPrf LTEZero
strengthenVarAndFSCommute (FS FZ) FZ = Refl
strengthenVarAndFSCommute (FS FZ) (FS k) = void $ contra2 $ FromNatPrf (LTESucc LTEZero)
strengthenVarAndFSCommute (FS (FS c)) FZ = Refl
strengthenVarAndFSCommute (FS (FS c)) (FS k) = cong FS $ strengthenVarAndFSCommute (FS c) k

shiftDownVarLT : (c, k : Fin (S n)) -> {prf : FinLTE c k} -> {neq : Not (c = k)} -> LTE (finToNat c) (finToNat (shiftDownVar c k prf neq))
shiftDownVarLT FZ FZ = void $ neq Refl
shiftDownVarLT FZ (FS k) = LTEZero
shiftDownVarLT (FS FZ) FZ {prf = FromNatPrf lte} = absurd lte
shiftDownVarLT (FS FZ) (FS FZ) = void $ neq Refl
shiftDownVarLT (FS FZ) (FS (FS k)) {prf = FromNatPrf (LTESucc lte)} = LTESucc LTEZero
shiftDownVarLT (FS (FS c)) FZ {prf = FromNatPrf lte} = absurd lte
shiftDownVarLT (FS (FS c)) (FS FZ) {prf = (FromNatPrf lte)} = absurd lte
shiftDownVarLT (FS (FS c)) (FS (FS k)) {prf = FromNatPrf (LTESucc lte)} = LTESucc (shiftDownVarLT (FS c) (FS k))

shiftDownVarAndFSCommute : (c, k : Fin (S n)) -> {0 prf : _} -> {0 prf2 : _} -> {0 neq : _} -> shiftDownVar (FS c) (FS k) prf neq = FS (shiftDownVar c k prf2 (neq . (cong FS)))
shiftDownVarAndFSCommute FZ FZ = void $ neq Refl
shiftDownVarAndFSCommute FZ (FS k) {prf = FromNatPrf (LTESucc lte)} = Refl
shiftDownVarAndFSCommute (FS c) FZ {prf2 = FromNatPrf lte} = void $ uninhabited lte
shiftDownVarAndFSCommute (FS c) (FS FZ) {prf = FromNatPrf (LTESucc lte)} = Refl
shiftDownVarAndFSCommute (FS c) (FS (FS k)) {prf = FromNatPrf (LTESucc lte)} {prf2 = FromNatPrf (LTESucc lte2)} = cong FS $ shiftDownVarAndFSCommute c (FS k)

lteAndNeqLT : {a, b: Nat} -> a `LTE` b -> Not (a = b) -> a `LT` b
lteAndNeqLT LTEZero neq {b = 0} = void $ neq Refl
lteAndNeqLT LTEZero neq {b = (S k)} = LTESucc LTEZero
lteAndNeqLT (LTESucc lte) neq = LTESucc (lteAndNeqLT lte (neq . (cong S)))

strengthenVarAndWeakenCommute : {n : _} -> (varDown : Fin (S n)) -> (k : Fin (S n)) -> {eqPrf1 : _} -> {eqPrf2 : _} ->
                                (contra3 : (FinLTE varDown k -> Void)) -> (contra2 : (FinLTE (FS varDown) (coerce eqPrf1 (weakenN 1 k)) -> Void)) ->
                                strengthenVar (FS varDown) (coerce eqPrf1 (weakenN 1 k)) contra2 = coerce eqPrf2 (weakenN 1 (strengthenVar varDown k contra3))
strengthenVarAndWeakenCommute varDown k contra3 contra2 =
  homoPointwiseIsEqual $ transitive (transitive (transitive (strengthenVarNeutral (FS varDown) _) (coerceEq eqPrf1)) (weakenNNeutral 1 k))
                                    (symmetric (transitive (transitive (coerceEq eqPrf2) (weakenNNeutral 1 _)) (strengthenVarNeutral varDown k)))

shiftDownShiftUpToShiftUpShiftDown_lemma_1 : {n : _} -> {k : Fin (S n)} -> {varDown : Fin (S n)} -> {varUp : Fin (S n)} -> (prf2 : FinLTE (FS varDown) (FS k)) -> FinLTE varUp varDown -> (neq : (FS varDown = FS k -> Void)) ->
                                             FinLTE (weaken varUp) (coerce (plusCommutative (S n) 1) (weakenN 1 k)) ->
                                             TyVar (shiftDownVar (FS varDown) (FS k) prf2 neq) = shiftUp (shiftDown (TyVar k) varDown (VarCanShiftDown k varDown (neq . (cong FS)))) 1 varUp
shiftDownShiftUpToShiftUpShiftDown_lemma_1 prf2 lte neq prf with (decide varDown k {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftDownShiftUpToShiftUpShiftDown_lemma_1 prf2 lte neq prf | (Yes prf3) with (decide varUp (coerce (plusCommutative n 1) (weakenN 1 (shiftDownVar varDown k prf3 (neq . (cong FS))))) {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
    shiftDownShiftUpToShiftUpShiftDown_lemma_1 prf2 lte neq prf | (Yes prf3) | (Yes prf4) = cong TyVar (shiftDownVarAndFSCommute varDown k)
    shiftDownShiftUpToShiftUpShiftDown_lemma_1 prf2 (FromNatPrf lte) neq (FromNatPrf prf) | (Yes prf3) | (No contra) =
      void $ contra $ FromNatPrf $ rewrite finToNatQuotient (transitive (coerceEq (plusCommutative n 1)) (weakenNNeutral 1 (shiftDownVar varDown k prf3 (neq . (cong FS))))) in
                                           transitive lte (shiftDownVarLT varDown k)
  shiftDownShiftUpToShiftUpShiftDown_lemma_1 (FromNatPrf (LTESucc prf2)) lte neq prf | (No contra) = void $ contra $ FromNatPrf prf2

shiftDownShiftUpToShiftUpShiftDown_lemma_2 : {n : _} -> (k : Fin (S n)) -> {varDown : Fin (S n)} -> {varUp : Fin (S n)} -> (contra : (FinLTE (FS varDown) (FS k) -> Void)) ->
                                             FinLTE varUp varDown -> (neq : (FS varDown = FS k -> Void)) -> FinLTE (weaken varUp) (coerce (plusCommutative (S n) 1) (weakenN 1 k)) ->
                                             TyVar (strengthenVar (FS varDown) (FS k) contra) = shiftUp (shiftDown (TyVar k) varDown (VarCanShiftDown k varDown (neq . (cong FS)))) 1 varUp
shiftDownShiftUpToShiftUpShiftDown_lemma_2 k contra lte neq prf with (decide varDown k {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftDownShiftUpToShiftUpShiftDown_lemma_2 k contra lte neq prf | (Yes (FromNatPrf prf2)) = void $ contra $ FromNatPrf $ LTESucc prf2
  shiftDownShiftUpToShiftUpShiftDown_lemma_2 k contra lte neq prf | (No contra2) with (decide varUp (coerce (plusCommutative n 1) (weakenN 1 (strengthenVar varDown k contra2))) {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
    shiftDownShiftUpToShiftUpShiftDown_lemma_2 k contra lte neq prf | (No contra2) | (Yes prf2) = cong TyVar (strengthenVarAndFSCommute varDown k)
    shiftDownShiftUpToShiftUpShiftDown_lemma_2 k contra lte neq (FromNatPrf prf) | (No contra2) | (No contra3) =
      void $ contra3 $ FromNatPrf $ rewrite sym (finToNatQuotient (weakenNeutral varUp)) in
                                    rewrite finToNatQuotient (transitive (transitive (coerceEq (plusCommutative n 1)) (weakenNNeutral 1 (strengthenVar varDown k contra2))) (strengthenVarNeutral varDown k)) in
                                    rewrite sym (finToNatQuotient (transitive (coerceEq (plusCommutative (S n) 1)) (weakenNNeutral 1 k))) in
                                            prf

shiftDownShiftUpToShiftUpShiftDown_lemma_3 : {n : _} -> (varDown : Fin (S n)) -> (k : Fin (S n)) -> (contra2 : (FinLTE (FS varDown) (coerce (plusCommutative (S n) 1) (weakenN 1 k)) -> Void)) -> (varUp : Fin (S n)) ->
                                             (lte : LTE (finToNat varUp) (finToNat varDown)) -> (FS varDown = coerce (plusCommutative (S n) 1) (weakenN 1 k) -> Void) ->
                                             (contra : (FinLTE (weaken varUp) (coerce (plusCommutative (S n) 1) (weakenN 1 k)) -> Void)) -> {0 neq : _} ->
                                             TyVar (strengthenVar (FS varDown) (coerce (plusCommutative (S n) 1) (weakenN 1 k)) contra2) = shiftUp (shiftDown (TyVar k) varDown (VarCanShiftDown k varDown neq)) 1 varUp
shiftDownShiftUpToShiftUpShiftDown_lemma_3 varDown k contra2 varUp lte neq_pred contra with (decide varDown k {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftDownShiftUpToShiftUpShiftDown_lemma_3 varDown k contra2 varUp lte neq_pred contra | (Yes (FromNatPrf prf)) =
    void $ contra2 $ FromNatPrf $ rewrite finToNatQuotient (transitive (coerceEq (plusCommutative (S n) 1)) (weakenNNeutral 1 k)) in
                                          lteAndNeqLT prf (neq . (injective {f=finToNat}))
  shiftDownShiftUpToShiftUpShiftDown_lemma_3 varDown k contra2 varUp lte neq_pred contra | (No contra3) with (decide varUp (coerce (plusCommutative n 1) (weakenN 1 (strengthenVar varDown k contra3)))
                                                                                                                     {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
    shiftDownShiftUpToShiftUpShiftDown_lemma_3 varDown k contra2 varUp lte neq_pred contra | (No contra3) | (Yes (FromNatPrf prf)) =
      void $ contra $ FromNatPrf $ rewrite finToNatQuotient (weakenNeutral varUp) in
                                   rewrite finToNatQuotient (transitive (coerceEq (plusCommutative (S n) 1)) (weakenNNeutral 1 k)) in
                                   rewrite sym (finToNatQuotient (transitive (transitive (coerceEq (plusCommutative n 1)) (weakenNNeutral 1 (strengthenVar varDown k contra3))) (strengthenVarNeutral varDown k))) in
                                           prf
    shiftDownShiftUpToShiftUpShiftDown_lemma_3 varDown k contra2 varUp lte neq_pred contra | (No contra3) | (No contra4) = cong TyVar (strengthenVarAndWeakenCommute varDown k contra3 contra2)

shiftDownShiftUpToShiftUpShiftDown : {n : _} -> (varUp : Fin (S n)) -> (varDown : Fin (S n)) -> (FinLTE varUp varDown) -> (ty : Ty (S n)) -> (shiftUpCanShiftDown : CanShiftDown (FS varDown) (shiftUp ty 1 (weaken varUp))) ->
                                     (canShiftDown : CanShiftDown varDown ty ** shiftDown (shiftUp ty 1 (weaken varUp)) (FS varDown) shiftUpCanShiftDown = shiftUp (shiftDown ty varDown canShiftDown) 1 varUp)
shiftDownShiftUpToShiftUpShiftDown varUp varDown lte (TyVar k) shiftUpCanShiftDown with (decide (weaken varUp) (coerce (plusCommutative (S n) 1) (weakenN 1 k)) {k=2} {ts=[Fin (1 + (S n)), Fin (1 + (S n))]} {p=FinLTE})
  shiftDownShiftUpToShiftUpShiftDown varUp varDown lte (TyVar k) (VarCanShiftDown (FS k) (FS varDown) neq) | (Yes prf) with (decide (FS varDown) (FS k) {k=2} {ts=[Fin (S (S n)), Fin (S (S n))]} {p=FinLTE})
    shiftDownShiftUpToShiftUpShiftDown varUp varDown lte (TyVar k) (VarCanShiftDown (FS k) (FS varDown) neq) | (Yes prf) | (Yes prf2) =
      (VarCanShiftDown k varDown (neq . (cong FS)) ** shiftDownShiftUpToShiftUpShiftDown_lemma_1 prf2 lte neq prf)
    shiftDownShiftUpToShiftUpShiftDown varUp varDown lte (TyVar k) (VarCanShiftDown (FS k) (FS varDown) neq) | (Yes prf) | (No contra) =
      (VarCanShiftDown k varDown (neq . (cong FS)) ** shiftDownShiftUpToShiftUpShiftDown_lemma_2 k contra lte neq prf)
  shiftDownShiftUpToShiftUpShiftDown varUp varDown lte (TyVar k) (VarCanShiftDown (coerce (plusCommutative (S n) 1) (weakenN 1 k)) (FS varDown) neq) | (No contra) with (decide (FS varDown) (coerce (plusCommutative (S n) 1) (weakenN 1 k)) {k=2} {ts=[Fin (S (S n)), Fin (S (S n))]} {p=FinLTE})
    shiftDownShiftUpToShiftUpShiftDown varUp varDown (FromNatPrf lte) (TyVar k) (VarCanShiftDown (coerce (plusCommutative (S n) 1) (weakenN 1 k)) (FS varDown) neq) | (No contra) | (Yes (FromNatPrf prf)) =
      void $ contra $ FromNatPrf $ rewrite finToNatQuotient (weakenNeutral varUp) in transitive lte (lteSuccLeft prf)
    shiftDownShiftUpToShiftUpShiftDown varUp varDown (FromNatPrf lte) (TyVar k) (VarCanShiftDown (coerce (plusCommutative (S n) 1) (weakenN 1 k)) (FS varDown) neq) | (No contra) | (No contra2) =
      (VarCanShiftDown k varDown (\eq => contra $ rewrite sym eq in
                                                          FromNatPrf $ rewrite finToNatQuotient (weakenNeutral varUp) in
                                                                       rewrite (finToNatQuotient (transitive (coerceEq (plusCommutative (S n) 1)) (weakenNNeutral 1 varDown))) in
                                                                               lte)
      ** shiftDownShiftUpToShiftUpShiftDown_lemma_3 varDown k contra2 varUp lte neq contra)
shiftDownShiftUpToShiftUpShiftDown varUp varDown lte (TyArr x y) (ArrCanShiftDown xCan yCan) =
  let (xCan' ** prfX) = shiftDownShiftUpToShiftUpShiftDown varUp varDown lte x xCan
      (yCan' ** prfY) = shiftDownShiftUpToShiftUpShiftDown varUp varDown lte y yCan
   in (ArrCanShiftDown xCan' yCan' ** cong2 TyArr prfX prfY)
shiftDownShiftUpToShiftUpShiftDown varUp varDown (FromNatPrf lte) (TyAll ty) (AllCanShiftDown canShift) =
  let (canShift' ** prf) = shiftDownShiftUpToShiftUpShiftDown (FS varUp) (FS varDown) (FromNatPrf (LTESucc lte)) ty canShift
   in (AllCanShiftDown canShift' ** cong TyAll prf)
shiftDownShiftUpToShiftUpShiftDown varUp varDown (FromNatPrf lte) (TySome ty) (SomeCanShiftDown canShift) =
  let (canShift' ** prf) = shiftDownShiftUpToShiftUpShiftDown (FS varUp) (FS varDown) (FromNatPrf (LTESucc lte)) ty canShift
   in (SomeCanShiftDown canShift' ** cong TySome prf)

export
shiftDownShiftUpBaseToShiftUpBaseShiftDown : {n : _} -> (varDown : Fin (S n)) -> (ty : Ty (S n)) -> (shiftUpCanShiftDown : CanShiftDown (FS varDown) (shiftUpBase ty 1)) ->
                                             (canShiftDown : CanShiftDown varDown ty ** shiftDown (shiftUpBase ty 1) (FS varDown) shiftUpCanShiftDown = shiftUpBase (shiftDown ty varDown canShiftDown) 1)
shiftDownShiftUpBaseToShiftUpBaseShiftDown varDown ty shiftUpCanShiftDown = shiftDownShiftUpToShiftUpShiftDown FZ varDown (FromNatPrf LTEZero) ty shiftUpCanShiftDown

canShiftDownToShiftUpCanShiftDown : {n : _} -> (varUp : Fin (S n)) -> (varDown : Fin (S n)) -> (FinLTE varUp varDown) -> (ty : Ty (S n)) ->
                                   (canShiftDown : CanShiftDown varDown ty) -> CanShiftDown (FS varDown) (shiftUp ty 1 (weaken varUp))
canShiftDownToShiftUpCanShiftDown varUp varDown lte (TyVar k) (VarCanShiftDown k varDown f) with (decide (weaken varUp) (coerce (plusCommutative (S n) 1) (weakenN 1 k)) {k=2} {ts=[Fin (S (S n)), Fin (S (S n))]} {p=FinLTE})
  canShiftDownToShiftUpCanShiftDown varUp varDown lte (TyVar k) (VarCanShiftDown k varDown f) | (Yes prf) = VarCanShiftDown (FS k) (FS varDown) (f . (injective {f=FS}))
  canShiftDownToShiftUpCanShiftDown varUp varDown (FromNatPrf lte) (TyVar k) (VarCanShiftDown k varDown f) | (No contra) =
    VarCanShiftDown _ (FS varDown) (\eq => contra $ FromNatPrf $ rewrite (finToNatQuotient $ weakenNeutral varUp) in transitive lte (rewrite sym eq in lteSuccRight reflexive))
canShiftDownToShiftUpCanShiftDown varUp varDown lte (TyArr fTy aTy) (ArrCanShiftDown x y) = ArrCanShiftDown (canShiftDownToShiftUpCanShiftDown varUp varDown lte fTy x) (canShiftDownToShiftUpCanShiftDown varUp varDown lte aTy y)
canShiftDownToShiftUpCanShiftDown varUp varDown (FromNatPrf lte) (TyAll bTy) (AllCanShiftDown x) = AllCanShiftDown (canShiftDownToShiftUpCanShiftDown (FS varUp) (FS varDown) (FromNatPrf (LTESucc lte)) bTy x)
canShiftDownToShiftUpCanShiftDown varUp varDown (FromNatPrf lte) (TySome bTy) (SomeCanShiftDown x) = SomeCanShiftDown (canShiftDownToShiftUpCanShiftDown (FS varUp) (FS varDown) (FromNatPrf (LTESucc lte)) bTy x)

export
canShiftDownToShiftUpBaseCanShiftDown : {n : _} -> (varDown : Fin (S n)) -> (ty : Ty (S n)) -> (canShiftDown : CanShiftDown varDown ty) ->
                                        CanShiftDown (FS varDown) (shiftUpBase ty 1)
canShiftDownToShiftUpBaseCanShiftDown varDown ty canShiftDown = canShiftDownToShiftUpCanShiftDown FZ varDown (FromNatPrf LTEZero) ty canShiftDown

export
shiftDownShiftUpBaseIsId : {n : _} -> (ty : Ty n) -> (tyCanShiftDown : CanShiftDown FZ (shiftUpBase ty 1)) -> (shiftDown (shiftUpBase ty 1) FZ tyCanShiftDown) = ty
shiftDownShiftUpBaseIsId ty tyCanShiftDown = shiftDownShiftUpIsId FZ ty tyCanShiftDown

export
substitute : {n : _} -> (var : Fin (S n)) -> (replacement : Ty (S n)) -> CanShiftDown var replacement -> (body : Ty (S n)) -> (ty : Ty (S n) ** CanShiftDown var ty)
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

fsShiftDownVarIsId : (var : Fin (S n)) -> (k : Fin (S n)) -> (prf : FinLTE var k) -> (f : (var = k -> Void)) -> FS (shiftDownVar var k prf f) = k
fsShiftDownVarIsId FZ FZ prf f = void $ f Refl
fsShiftDownVarIsId FZ (FS k) prf f = Refl
fsShiftDownVarIsId (FS var) FZ (FromNatPrf lte) f = absurd lte
fsShiftDownVarIsId (FS var) (FS FZ) prf f = Refl
fsShiftDownVarIsId (FS var) (FS (FS k)) (FromNatPrf (LTESucc prf)) f = cong FS $ fsShiftDownVarIsId var (FS k) (FromNatPrf prf) (f . (cong FS))

export
shiftDownCanShiftDown : {n : _} -> (ty : Ty (S (S n))) ->  (var : Fin (S (S n))) -> (varOther : Fin (S n)) -> (canShiftDownVar : CanShiftDown var ty) -> FinLTE var (weaken varOther) ->
                        CanShiftDown (FS varOther) ty -> CanShiftDown varOther (shiftDown ty var canShiftDownVar)
shiftDownCanShiftDown (TyVar k) var varOther (VarCanShiftDown k var f) varLTEvarOther canShiftDownVarOther with (decide var k {k=2} {ts=[Fin (S (S n)), Fin (S (S n))]} {p=FinLTE})
  shiftDownCanShiftDown (TyVar k) var varOther (VarCanShiftDown k var f) varLTEvarOther (VarCanShiftDown k (FS varOther) f2) | (Yes prf) =
    VarCanShiftDown (shiftDownVar var k prf f) varOther (\eq => f2 (trans (cong FS eq) (fsShiftDownVarIsId var k prf f)))
  shiftDownCanShiftDown (TyVar k) var varOther (VarCanShiftDown k var f) varLTEvarOther canShiftDownVarOther | (No contra) =
    VarCanShiftDown (strengthenVar var k contra) varOther
                    (\eq => contra (transitive varLTEvarOther 
                                               (FromNatPrf $ rewrite eq in
                                                             rewrite finToNatQuotient $ transitive (weakenNeutral (strengthenVar var k contra)) (strengthenVarNeutral var k) in
                                                                     reflexive)))
shiftDownCanShiftDown (TyArr fTy aTy) var varOther (ArrCanShiftDown fCanShiftVar aCanShiftVar) varLTEvarOther (ArrCanShiftDown fCanShiftVarOther aCanShiftVarOther) =
  ArrCanShiftDown (shiftDownCanShiftDown fTy var varOther fCanShiftVar varLTEvarOther fCanShiftVarOther) (shiftDownCanShiftDown aTy var varOther aCanShiftVar varLTEvarOther aCanShiftVarOther)
shiftDownCanShiftDown (TyAll bTy) var varOther (AllCanShiftDown bCanShiftVar) (FromNatPrf varLTEvarOther) (AllCanShiftDown bCanShiftVarOther) =
  AllCanShiftDown $ shiftDownCanShiftDown bTy (FS var) (FS varOther) bCanShiftVar (FromNatPrf (LTESucc varLTEvarOther)) bCanShiftVarOther
shiftDownCanShiftDown (TySome bTy) var varOther (SomeCanShiftDown bCanShiftVar) (FromNatPrf varLTEvarOther) (SomeCanShiftDown bCanShiftVarOther) =
  SomeCanShiftDown $ shiftDownCanShiftDown bTy (FS var) (FS varOther) bCanShiftVar (FromNatPrf (LTESucc varLTEvarOther)) bCanShiftVarOther

shiftUpCanShiftDownOther : {n : _} -> (ty : Ty (S n)) -> {var : Fin (S (S n))} -> {varOther : Fin (S n)} -> FinLTE var (weaken varOther) -> CanShiftDown varOther ty -> CanShiftDown (FS varOther) (shiftUp ty 1 var)
shiftUpCanShiftDownOther (TyVar k) lte canShiftDownOther with (decide var (coerce (plusCommutative (S n) 1) (weakenN 1 k)) {k=2} {ts=[Fin (S (S n)), Fin (S (S n))]} {p=FinLTE})
  shiftUpCanShiftDownOther (TyVar k) lte (VarCanShiftDown k varOther neq) | (Yes prf) = VarCanShiftDown (FS k) (FS varOther) (neq . injective)
  shiftUpCanShiftDownOther (TyVar k) (FromNatPrf lte) (VarCanShiftDown k varOther neq) | (No contra) =
    VarCanShiftDown (coerce (plusCommutative (S n) 1) (weakenN 1 k)) (FS varOther) (\eq => contra $ rewrite sym eq in FromNatPrf $ lteSuccRight (rewrite sym (finToNatQuotient $ weakenNeutral varOther) in lte))
shiftUpCanShiftDownOther (TyArr x y) lte (ArrCanShiftDown z w) = ArrCanShiftDown (shiftUpCanShiftDownOther x lte z) (shiftUpCanShiftDownOther y lte w)
shiftUpCanShiftDownOther (TyAll x) (FromNatPrf lte) (AllCanShiftDown y) = AllCanShiftDown (shiftUpCanShiftDownOther x (FromNatPrf (LTESucc lte)) y)
shiftUpCanShiftDownOther (TySome x) (FromNatPrf lte) (SomeCanShiftDown y) = SomeCanShiftDown (shiftUpCanShiftDownOther x (FromNatPrf (LTESucc lte)) y)

substituteCanShiftDown : {n : _} -> {var, varOther : Fin (S n)} -> FinLTE (FS var) (weaken varOther) -> (body : Ty (S n)) -> {replacement : Ty (S n)} -> {replacementCanShiftDownVar : CanShiftDown var replacement} ->
                         CanShiftDown varOther replacement -> CanShiftDown varOther body -> CanShiftDown varOther (substitute var replacement replacementCanShiftDownVar body).fst
substituteCanShiftDown lte (TyVar k) replacementCanShiftOther bodyCanShiftOther with (decEq var k)
  substituteCanShiftDown lte (TyVar k) replacementCanShiftOther bodyCanShiftOther | (Yes prf) = replacementCanShiftOther
  substituteCanShiftDown lte (TyVar k) replacementCanShiftOther bodyCanShiftOther | (No contra) = bodyCanShiftOther
substituteCanShiftDown lte (TyArr x y) replacementCanShiftOther bodyCanShiftOther with (substitute var replacement replacementCanShiftDownVar x) proof xPrf
  substituteCanShiftDown lte (TyArr x y) replacementCanShiftOther bodyCanShiftOther | (xSub ** xCanShift) with (substitute var replacement replacementCanShiftDownVar y) proof yPrf
    substituteCanShiftDown lte (TyArr x y) replacementCanShiftOther (ArrCanShiftDown xVarOther yVarOther) | (xSub ** xCanShift) | (ySub ** yCanShift) =
      ArrCanShiftDown (rewrite sym (cong fst xPrf) in substituteCanShiftDown lte x replacementCanShiftOther xVarOther)
                      (rewrite sym (cong fst yPrf) in substituteCanShiftDown lte y replacementCanShiftOther yVarOther)
substituteCanShiftDown (FromNatPrf lte) (TyAll x) replacementCanShiftOther (AllCanShiftDown xVarOther) with (substitute (FS var) (shiftUp replacement 1 (FS var)) (shiftUpCanShiftDown replacement (FS var)) x) proof prf
  substituteCanShiftDown (FromNatPrf lte) (TyAll x) replacementCanShiftOther (AllCanShiftDown xVarOther) | (xSub ** xCanShift) =
    AllCanShiftDown (rewrite sym (cong fst prf) in substituteCanShiftDown (FromNatPrf (LTESucc lte)) x (shiftUpCanShiftDownOther replacement (FromNatPrf lte) replacementCanShiftOther) xVarOther)
substituteCanShiftDown (FromNatPrf lte) (TySome x) replacementCanShiftOther (SomeCanShiftDown xVarOther) with (substitute (FS var) (shiftUp replacement 1 (FS var)) (shiftUpCanShiftDown replacement (FS var)) x) proof prf
  substituteCanShiftDown (FromNatPrf lte) (TySome x) replacementCanShiftOther (SomeCanShiftDown xVarOther) | (xSub ** xCanShift) =
    SomeCanShiftDown (rewrite sym (cong fst prf) in substituteCanShiftDown (FromNatPrf (LTESucc lte)) x (shiftUpCanShiftDownOther replacement (FromNatPrf lte) replacementCanShiftOther) xVarOther)

export
substituteFirst : {n : _} -> (replacement : Ty n) -> (body : Ty (S n)) -> Ty n
substituteFirst replacement body = shiftDown (fst $ substitute FZ (shiftUp replacement 1 FZ) (shiftUpCanShiftDown replacement FZ) body) FZ (snd $ substitute FZ (shiftUp replacement 1 FZ) (shiftUpCanShiftDown replacement FZ) body)

export
substituteFirstCanShiftDown : {n : _} -> {var : Fin (S n)} -> {replacement : Ty (S n)} -> {body : Ty (S (S n))} ->
                              CanShiftDown var replacement -> CanShiftDown (FS var) body -> CanShiftDown var (substituteFirst replacement body)
substituteFirstCanShiftDown replacementCanShift bodyCanShift =
  shiftDownCanShiftDown _ FZ var _ (FromNatPrf LTEZero) (substituteCanShiftDown (FromNatPrf (LTESucc LTEZero)) _ (shiftUpCanShiftDownOther replacement (FromNatPrf LTEZero) replacementCanShift) bodyCanShift)

--CanShiftDown var (shiftDown ((substitute FZ (shiftUp replacement 1 FZ) (shiftUpCanShiftDown replacement FZ) body) .fst) FZ ((substitute FZ (shiftUp replacement 1 FZ) (shiftUpCanShiftDown replacement FZ) body) .snd))


public export
countDown : (n : Nat) -> Vect n Nat
countDown 0 = []
countDown (S k) = k :: countDown k

public export
Tys : Nat -> Type
Tys k = All Ty (countDown k)

--export
--substituteMany : {m, n : Nat} -> (replacements : Tys n) -> (body : Ty (m + n)) -> Ty m
--substituteMany [] body = rewrite sym $ plusZeroRightNeutral m in  body
--substituteMany (ty :: tys) body {n = S n} = let newBody  = substituteMany tys {m = S m} (rewrite plusSuccRightSucc m n in body)
--                                                newTy = rewrite sym $ plusZeroRightNeutral m in shiftUpBase (substituteMany tys {m = 0} ty) m
--                                                (subbed ** subbedCanShift) = substitute FZ (shiftUp newTy 1 FZ) (shiftUpCanShiftDown newTy FZ) newBody
--                                             in shiftDown subbed FZ subbedCanShift
--
--export
--substituteManyNoneNeutral : {m : Nat} -> (body : Ty (m + 0)) -> substituteMany {m} {n = 0} [] body = (rewrite sym $ plusZeroRightNeutral m in body)

export
Injective TyAll where
  injective Refl = Refl

export
Injective TySome where
  injective Refl = Refl

export
tyArrBiinjective : TyArr w x = TyArr y z -> (w = y, x = z)
tyArrBiinjective Refl = (Refl, Refl)

export
shiftDownAndSubstituteCommutes : ()

export
shiftDownCommutes : (varA, varB : Fin (S n)) -> (ty : Ty (S (S n))) -> (canShiftDownB1 : _) -> (canShiftDownA1 : _) -> (canShiftDownA2 : _) -> (canShiftDownB2 : _) -> shiftDown (shiftDown ty (FS varB) canShiftDownB1) varA canShiftDownA1 = shiftDown (shiftDown ty (weaken varA) canShiftDownA2) varB canShiftDownB2

export
shiftDownAndSubstituteFirstCommute : (var : Fin (S n)) -> (arg : Ty (S n)) -> (bTy : Ty (S (S n))) ->
                                     (tyCanShiftDown : CanShiftDown var (substituteFirst arg bTy)) -> (argCanShiftDown : CanShiftDown var arg) -> (bTyCanShiftDown : CanShiftDown (FS var) bTy) ->
                                     shiftDown (substituteFirst arg bTy) var tyCanShiftDown = substituteFirst (shiftDown arg var argCanShiftDown) (shiftDown bTy (FS var) bTyCanShiftDown)
shiftDownAndSubstituteFirstCommute var arg bTy tyCanShiftDown argCanShiftDown bTyCanShiftDown = ?shiftDownAndSubstituteFirstCommute_rhs

--shiftDown : (ty : Ty (S n)) -> (c : Fin (S n)) -> CanShiftDown c ty -> Ty n
--shiftDown (TyVar k) c (VarCanShiftDown k c f) with (decide c k {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
--  shiftDown (TyVar k) c (VarCanShiftDown k c f) | (Yes prf) = TyVar (shiftDownVar c k prf f)
--  shiftDown (TyVar k) c (VarCanShiftDown k c f) | (No contra) = TyVar (strengthenVar c k contra)
--shiftDown (TyArr fTy aTy) c (ArrCanShiftDown x y) = TyArr (shiftDown fTy c x) (shiftDown aTy c y)
--shiftDown (TyAll bTy) c (AllCanShiftDown x) = TyAll (shiftDown bTy (FS c) x)
--shiftDown (TySome bTy) c (SomeCanShiftDown x) = TySome (shiftDown bTy (FS c) x)
