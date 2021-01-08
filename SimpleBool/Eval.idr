module Eval

import Control.WellFounded
import Data.Nat
import Data.Fin
import Data.Fin.Order
import Decidable.Equality
import Decidable.Decidable
import Decidable.Order
import Data.Rel
import Data.Fun
import Data.Fuel

import Parser

%default total

export
getType : {n : Nat} -> Context n -> Term n -> Either String Ty
getType context (TmVar x) = case getBinding context x of
                                   NameBind => Left "Unbound name"
                                   (VarBind type) => Right type
getType context (TmAbs name varTy body) = TyArr varTy <$> getType (addBinding context name varTy) body
getType context (TmApp x y) = do funcTy <- getType context x
                                 subTy <- getType context y
                                 case funcTy of
                                      TyArr var return => case decEq var subTy of
                                                               (Yes prf) => Right return
                                                               (No contra) => Left "Expected type of application does not match passed type"
                                      _ => Left "Expected function type in application"
getType context TmTrue = Right TyBool
getType context TmFalse = Right TyBool
getType context (TmIf g t e) = do TyBool <- getType context g
                                    | _ => Left "Guard of if statement must be Bool"
                                  thenTy <- getType context t
                                  elseTy <- getType context e
                                  case decEq thenTy elseTy of
                                       (Yes prf) => Right thenTy
                                       (No contra) => Left "Both branches of the if statement must be the same type"

data IsValue : Term n -> Type where
  AbsIsValue : IsValue (TmAbs name ty body)
  TrueIsValue : IsValue TmTrue
  FalseIsValue : IsValue TmFalse

Uninhabited (IsValue (TmVar j)) where
  uninhabited AbsIsValue impossible
  uninhabited TrueIsValue impossible
  uninhabited FalseIsValue impossible

Uninhabited (IsValue (TmApp x y)) where
  uninhabited AbsIsValue impossible
  uninhabited TrueIsValue impossible
  uninhabited FalseIsValue impossible

Uninhabited (IsValue (TmIf g t e)) where
  uninhabited AbsIsValue impossible
  uninhabited TrueIsValue impossible
  uninhabited FalseIsValue impossible

isValue : (t : Term n) -> Dec (IsValue t)
isValue (TmVar j) = No uninhabited
isValue (TmAbs name ty body) = Yes AbsIsValue
isValue (TmApp x y) = No uninhabited
isValue TmTrue = Yes TrueIsValue
isValue TmFalse = Yes FalseIsValue
isValue (TmIf g t e) = No uninhabited

shiftUp : (c : Fin (S n)) -> Term n -> Term (S n)
shiftUp c (TmVar k) with (decide c (weaken k) {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftUp c (TmVar k) | (Yes prf) = TmVar (FS k)
  shiftUp c (TmVar k) | (No contra) = TmVar (weaken k)
shiftUp c (TmAbs nm ty body) = TmAbs nm ty (shiftUp (FS c) body)
shiftUp c (TmApp x y) = TmApp (shiftUp c x) (shiftUp c y)
shiftUp c TmTrue = TmTrue
shiftUp c TmFalse = TmFalse
shiftUp c (TmIf g t e) = TmIf (shiftUp c g) (shiftUp c t) (shiftUp c e)

data CanShiftDown : (c : Fin (S n)) -> Term (S n) -> Type where
  VarCanShiftDown : (k : Fin (S n)) -> (c : Fin (S n)) -> Not (c = k) -> CanShiftDown c (TmVar k)
  AppCanShiftDown : CanShiftDown c x -> CanShiftDown c y -> CanShiftDown c (TmApp x y)
  AbsCanShiftDown : CanShiftDown (FS c) body -> CanShiftDown c (TmAbs nm ty body)
  TrueCanShiftDown : CanShiftDown c TmTrue
  FalseCanShiftDown : CanShiftDown c TmFalse
  IfCanShiftDown : CanShiftDown c g -> CanShiftDown c t -> CanShiftDown c e -> CanShiftDown c (TmIf g t e)

shiftVarDown : (c : Fin n) -> (var : Fin (S n)) -> Not (weaken c = var) -> Fin n
shiftVarDown FZ FZ prf = void $ prf Refl
shiftVarDown FZ (FS x) prf = x
shiftVarDown (FS x) FZ prf = FZ
shiftVarDown (FS x) (FS y) prf = FS (shiftVarDown x y (\Refl => prf Refl))

lteZeroIsEqZero : {c : Fin (S n)} -> FinLTE c FZ -> c = FZ
lteZeroIsEqZero {c = FZ} _ = Refl
lteZeroIsEqZero (FromNatPrf (LTESucc x)) impossible

strengthenVar : (c : Fin (S n)) -> (var : Fin (S n)) -> (FinLTE c var -> Void) -> Fin n
strengthenVar FZ _ notLTE = void $ notLTE (FromNatPrf LTEZero)
strengthenVar (FS FZ) FZ _ = FZ
strengthenVar (FS (FS _)) FZ _ = FZ
strengthenVar (FS FZ) (FS var) notLTE = void $ notLTE (FromNatPrf (LTESucc LTEZero))
strengthenVar (FS (FS c)) (FS var) notLTE = FS (strengthenVar (FS c) var (\(FromNatPrf lte) => notLTE $ FromNatPrf (LTESucc lte)))

shiftDown : (c : Fin (S n)) -> (term : Term (S n)) -> (CanShiftDown c term) -> Term n
shiftDown c (TmVar var) (VarCanShiftDown var c prf) with (decide c var {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftDown c (TmVar FZ) (VarCanShiftDown FZ c prf) | (Yes lte) = void $ prf (lteZeroIsEqZero lte)
  shiftDown c (TmVar (FS var)) (VarCanShiftDown (FS var) c prf) | (Yes _) = TmVar var
  shiftDown c (TmVar var) (VarCanShiftDown var c prf) | (No contra) = TmVar $ strengthenVar c var contra
shiftDown c (TmAbs nm ty body) (AbsCanShiftDown prf) = TmAbs nm ty (shiftDown (FS c) body prf)
shiftDown c (TmApp x y) (AppCanShiftDown prfX prfY) = TmApp (shiftDown c x prfX) (shiftDown c y prfY)
shiftDown c TmTrue TrueCanShiftDown = TmTrue
shiftDown c TmFalse FalseCanShiftDown = TmFalse
shiftDown c (TmIf g t e) (IfCanShiftDown sg st se) = TmIf (shiftDown c g sg) (shiftDown c t st) (shiftDown c e se)

substitute : (var : Fin n) -> (tReplace : Term n) -> (tBody : Term n) -> Term n
substitute var tReplace (TmVar x) with (decEq x var)
  substitute var tReplace (TmVar var) | (Yes Refl) = tReplace
  substitute var tReplace (TmVar x) | (No _) = TmVar x
substitute var tReplace (TmAbs name ty body) = let newBody = substitute (FS var) (shiftUp 0 tReplace) body in
                                                   TmAbs name ty newBody
substitute var tReplace (TmApp x y) = let x' = substitute var tReplace x
                                          y' = substitute var tReplace y in
                                          TmApp x' y'
substitute var tReplace TmTrue = TmTrue
substitute var tReplace TmFalse = TmFalse
substitute var tReplace (TmIf g t e) = TmIf (substitute var tReplace g) (substitute var tReplace t) (substitute var tReplace e)

finToNatEqFinToNatWeaken : (a : Fin n) -> finToNat a = finToNat (weaken a)
finToNatEqFinToNatWeaken FZ = Refl
finToNatEqFinToNatWeaken (FS a) = cong S (finToNatEqFinToNatWeaken a)

notFinLTEImpliesGT : {a : Fin (S n)} -> {b : Fin n} -> (FinLTE a (weaken b) -> Void) -> (FinLTE (FS b) a)
notFinLTEImpliesGT notLTE = FromNatPrf (notLTEImpliesGT (rewrite finToNatEqFinToNatWeaken b in  notLTE . FromNatPrf))

substituteCanShiftDown : (var : Fin (S n)) -> (tReplace : Term (S n)) -> (tBody : Term (S n)) -> (CanShiftDown var tReplace) -> CanShiftDown var (substitute var tReplace tBody)
substituteCanShiftDown var tReplace (TmVar x) prf with (decEq x var)
  substituteCanShiftDown var tReplace (TmVar var) prf | (Yes Refl) = prf
  substituteCanShiftDown var tReplace (TmVar x) prf | (No contra) = VarCanShiftDown x var (\Refl => contra Refl)
substituteCanShiftDown var tReplace (TmAbs nm ty body) prf = AbsCanShiftDown (substituteCanShiftDown (FS var) (shiftUp 0 tReplace) body (help var 0 tReplace (FromNatPrf LTEZero) prf))
  where
    help3 : {var', k : Fin m} -> FinLTE (FS k) (weaken var') -> FS var' = weaken k -> Void
    help3 {var' = var'} {k = FZ} lte Refl impossible
    help3 (FromNatPrf LTEZero) Refl impossible

    help2 : (c : Fin (S (S m))) -> (k : Fin (S m)) -> (var' : Fin (S m)) -> (FinLTE c (weaken k) -> Void) -> FinLTE c (weaken var') -> FS var' = weaken k -> Void
    help2 c k var' cNotLteK cLteVar fsVarEqK = help3 (transitive (FS k) c (weaken var') (notFinLTEImpliesGT cNotLteK) cLteVar) fsVarEqK

    help : {0 m : Nat} -> (var' : Fin (S m)) -> (c : Fin (S (S m))) -> (tReplace : Term (S m)) -> FinLTE c (weaken var') -> CanShiftDown var' tReplace -> CanShiftDown (FS var') (shiftUp c tReplace)
    help {m} var' c (TmVar k) lte (VarCanShiftDown k var' prff) with (decide c (weaken k) {k=2} {ts=[Fin (S (S m)), Fin (S (S m))]} {p=FinLTE})
      help var' c (TmVar k) lte (VarCanShiftDown k var' prff) | (Yes _) = VarCanShiftDown (FS k) (FS var') (\Refl => prff Refl)
      help var' c (TmVar k) lte (VarCanShiftDown k var' prff) | (No contra) = VarCanShiftDown (weaken k) (FS var') (help2 c k var' contra lte)
    help var' c (TmAbs name ty z) (FromNatPrf lte) (AbsCanShiftDown prff) = AbsCanShiftDown (help (FS var') (FS c) z (FromNatPrf (LTESucc lte)) prff)
    help var' c (TmApp x y) lte (AppCanShiftDown px py) = AppCanShiftDown (help var' c x lte px) (help var' c y lte py)
    help var' c TmTrue lte TrueCanShiftDown = TrueCanShiftDown
    help var' c TmFalse lte FalseCanShiftDown = FalseCanShiftDown
    help var' c (TmIf g t e) lte (IfCanShiftDown x y z) = IfCanShiftDown (help var' c g lte x) (help var' c t lte y) (help var' c e lte z)
substituteCanShiftDown var tReplace (TmApp x y) prff = AppCanShiftDown (substituteCanShiftDown var tReplace x prff) (substituteCanShiftDown var tReplace y prff)
substituteCanShiftDown var tReplace TmTrue prf = TrueCanShiftDown
substituteCanShiftDown var tReplace TmFalse prf = FalseCanShiftDown
substituteCanShiftDown var tReplace (TmIf g t e) prf = IfCanShiftDown (substituteCanShiftDown var tReplace g prf) (substituteCanShiftDown var tReplace t prf) (substituteCanShiftDown var tReplace e prf)

succNotLteSelf : (c : Fin (S n)) -> (k : Fin n) -> FinLTE c (weaken k) -> c = FS k -> Void
succNotLteSelf FZ k (FromNatPrf LTEZero) Refl impossible
succNotLteSelf (FS c) FZ (FromNatPrf (LTESucc lte)) eq impossible
succNotLteSelf (FS c) (FS k) (FromNatPrf (LTESucc lte)) eq = succNotLteSelf c k (FromNatPrf lte) (fsInjective eq)

shiftUpCanShiftDown : (c : Fin (S n)) -> (term : Term n) -> CanShiftDown c (shiftUp c term)
shiftUpCanShiftDown c (TmVar k) with (decide c (weaken k) {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftUpCanShiftDown c (TmVar k) | (Yes prf) = VarCanShiftDown (FS k) c (succNotLteSelf c k prf)
  shiftUpCanShiftDown c (TmVar k) | (No contra) = VarCanShiftDown (weaken k) c (\eq => contra $ rewrite eq in FromNatPrf lteRefl)
shiftUpCanShiftDown c (TmAbs nm ty body) = AbsCanShiftDown (shiftUpCanShiftDown (FS c) body)
shiftUpCanShiftDown c (TmApp x y) = AppCanShiftDown (shiftUpCanShiftDown c x) (shiftUpCanShiftDown c y)
shiftUpCanShiftDown c TmTrue = TrueCanShiftDown
shiftUpCanShiftDown c TmFalse = FalseCanShiftDown
shiftUpCanShiftDown c (TmIf g t e) = IfCanShiftDown (shiftUpCanShiftDown c g) (shiftUpCanShiftDown c t) (shiftUpCanShiftDown c e)

oneStep : (tIn : Term n) -> Maybe (Term n)
oneStep (TmVar _) = Nothing
oneStep (TmAbs _ _ body) = Nothing
oneStep (TmApp x y) with (isValue x)
  oneStep (TmApp x y) | (No _) = do x' <- oneStep x
                                    pure $ TmApp x' y
  oneStep (TmApp x y) | (Yes prf) with (isValue y)
    oneStep (TmApp x y) | (Yes _) | (No _) = do y' <- oneStep y
                                                pure $ TmApp x y'
    oneStep (TmApp (TmAbs _ _ body) y) | (Yes AbsIsValue) | (Yes _) = Just $ shiftDown FZ (substitute FZ (shiftUp FZ y) body) (substituteCanShiftDown FZ (shiftUp FZ y) body (shiftUpCanShiftDown FZ y))
    oneStep (TmApp _ y) | (Yes _) | (Yes _) = Nothing --type error
oneStep TmTrue = Nothing
oneStep TmFalse = Nothing
oneStep (TmIf g t e) with (isValue g)
  oneStep (TmIf TmTrue t e) | (Yes TrueIsValue) = Just t
  oneStep (TmIf TmFalse t e) | (Yes FalseIsValue) = Just e
  oneStep (TmIf (TmAbs name ty body) t e) | (Yes AbsIsValue) = Nothing --type error
  oneStep (TmIf g t e) | (No contra) = do g' <- oneStep g
                                          pure (TmIf g' t e)

export
covering
eval : Term n -> Term n
eval term = case oneStep term of
                 Nothing => term
                 (Just term') => eval term'

export
totalEval : Term n -> Fuel -> Term n
totalEval term Dry = term
totalEval term (More fuel) = case oneStep term of
                                  Nothing => term
                                  (Just term') => totalEval term' fuel

export
bigStepEval : Term n -> Maybe (Term n)
