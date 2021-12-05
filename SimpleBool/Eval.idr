module Eval

import Control.WellFounded
import Data.Nat
import Data.Fin
import Data.Fin.Order
import Decidable.Equality
import Decidable.Decidable
--import Decidable.Order
import Data.Rel
import Data.Fun
import Data.Fuel
import Data.DPair
import Data.HVect

import Parser

%default total

data HasType : {n : Nat} -> Context n -> Term n -> Ty -> Type where
  VarHasType : getBindingType context v = type -> HasType context (TmVar v) type
  AbsHasType : (bodyHasType : HasType (addBinding context name varTy) body type) -> HasType context (TmAbs name varTy body) (TyArr varTy type)
  AppHasType : {varTy : Ty} -> (xHasType : HasType context x (TyArr varTy returnTy)) -> (yHasType : HasType context y varTy) -> HasType context (TmApp x y) returnTy
  TrueHasType : HasType context TmTrue TyBool
  FalseHasType : HasType context TmFalse TyBool
  IfHasType : (gHasType : HasType context g TyBool) -> (tHasType : HasType context t type) -> (eHasType : HasType context e type) -> HasType context (TmIf g t e) type

Uninhabited (HasType context TmTrue (TyArr tyIn tyOut)) where
  uninhabited (VarHasType prf) impossible
  uninhabited (AbsHasType x) impossible
  uninhabited (AppHasType x y) impossible
  uninhabited TrueHasType impossible
  uninhabited FalseHasType impossible
  uninhabited (IfHasType x y z) impossible

Uninhabited (HasType context TmFalse (TyArr tyIn tyOut)) where
  uninhabited (VarHasType prf) impossible
  uninhabited (AbsHasType x) impossible
  uninhabited (AppHasType x y) impossible
  uninhabited TrueHasType impossible
  uninhabited FalseHasType impossible
  uninhabited (IfHasType x y z) impossible

Uninhabited (HasType [] (TmAbs name ty body) TyBool) where
  uninhabited (VarHasType prf) impossible
  uninhabited (AbsHasType x) impossible
  uninhabited (AppHasType x y) impossible
  uninhabited TrueHasType impossible
  uninhabited FalseHasType impossible
  uninhabited (IfHasType x y z) impossible

withProof : (x : t) -> (y : t ** x = y)
withProof x = (x ** Refl)

export
getType : {n : Nat} -> (context : Context n) -> (term : Term n) -> Either String (type : Ty ** (HasType context term type))
getType context (TmVar x) = Right (getBindingType context x ** VarHasType Refl)
getType context (TmAbs name varTy body) = do (bodyType ** bodyHasType) <- getType (addBinding context name varTy) body
                                             pure (TyArr varTy bodyType ** AbsHasType bodyHasType)
getType context (TmApp x y) = do ((TyArr var return) ** funcHasType) <- getType context x
                                    | _ => Left "Expected function type in application"
                                 (subTy ** subHasType) <- getType context y
                                 case decEq var subTy of
                                      (Yes Refl) => Right (return ** (AppHasType funcHasType subHasType))
                                      (No _) => Left "Exptected type of application does not match passed type"
getType context TmTrue = Right (TyBool ** TrueHasType)
getType context TmFalse = Right (TyBool ** FalseHasType)
getType context (TmIf g t e) = do (TyBool ** guardHasType) <- getType context g
                                    | _ => Left "Guard of if statement must be Bool"
                                  (thenTy ** thenHasType) <- getType context t
                                  (elseTy ** elseHasType) <- getType context e
                                  case decEq thenTy elseTy of
                                       (Yes (Refl {x=retTy})) => Right (retTy ** (IfHasType guardHasType thenHasType elseHasType))
                                       (No _) => Left "Both branches of the if statement must be the same type"

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

shiftDown : (c : Fin (S n)) -> (term : Term (S n)) -> (0 shiftable : CanShiftDown c term) -> Term n
shiftDown c (TmVar var) (VarCanShiftDown var c prf) with (decide c var {k=2} {ts=[Fin (S n), Fin (S n)]} {p=FinLTE})
  shiftDown c (TmVar var) (VarCanShiftDown var c prf) | (No contra) = TmVar $ strengthenVar c var contra
  shiftDown c (TmVar FZ) (VarCanShiftDown FZ c prf) | (Yes lte) = void $ prf (lteZeroIsEqZero lte)
  shiftDown c (TmVar (FS var)) (VarCanShiftDown (FS var) c prf) | (Yes _) = TmVar var
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
  shiftUpCanShiftDown c (TmVar k) | (No contra) = VarCanShiftDown (weaken k) c (\eq => contra $ rewrite eq in FromNatPrf (reflexive {rel=LTE}))
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

Sized (HasType context t ty) where
  size (VarHasType prf) = 1
  size (AbsHasType bodyHasType) = S (size bodyHasType)
  size (AppHasType x y) = (size x) + (size y)
  size TrueHasType = 1
  size FalseHasType = 1
  size (IfHasType g t e) = (size g) + (size t) + (size e)

BigStepResult : (ty : Ty) -> Type
BigStepResult TyBool = (t : Term 0 ** (IsValue t, HasType [] t TyBool))
BigStepResult (TyArr tyIn tyOut) = ((t : Term 0 ** (IsValue t, HasType [] t (TyArr tyIn tyOut))), (BigStepResult tyIn) -> (BigStepResult tyOut))

valueOnly : {ty : Ty} -> BigStepResult ty -> (t : Term 0 ** (IsValue t, HasType [] t ty))
valueOnly {ty = TyBool} x = x
valueOnly {ty = (TyArr _ _)} (x,_) = x

typeNamesToContext : (types : Vect n Ty) -> (names : Vect n String) -> Context n
typeNamesToContext [] [] = []
typeNamesToContext (ty :: types) (nm :: names) = addBinding (typeNamesToContext types names) nm ty

mapIndexCommutitive : (vect : Vect n a) -> (ind : Fin n) -> (f : a -> b) -> (f (index ind vect) = index ind (map f vect))
mapIndexCommutitive (x :: xs) FZ f = Refl
mapIndexCommutitive (x :: xs) (FS ind) f = mapIndexCommutitive xs ind f

typeNamesHelp : {v : Fin n} -> {types : Vect n Ty} -> {names : Vect n String} -> snd (index v (typeNamesToContext types names)) = tyOut -> (tyOut = index v types)
typeNamesHelp {v = FZ} {types = (ty :: types)} {names = (nm :: names)} Refl = Refl
typeNamesHelp {v = FS v} {types = (ty :: types)} {names = (nm :: names)} prf = typeNamesHelp prf

splitSumID : {a : Nat} -> (k : Fin (a + b)) -> Either (j : Fin a ** weakenN b j = k) (j : Fin b ** shift a j = k)
splitSumID {a = Z} k = Right (k ** Refl)
splitSumID {a = (S n)} FZ = Left (FZ ** Refl)
splitSumID {a = (S n)} (FS x) = case splitSumID x of
                                     (Left (k' ** prf)) => Left (FS k' ** cong FS prf)
                                     (Right (k' ** prf)) => Right (k' ** cong FS prf)

keepTypeMatches : {n : Nat} -> (x : Fin (n + m)) -> (y : Fin n) ->
                  (namesSub : Vect m String) -> (typesSub : Vect m Ty) ->
                  (namesStay : Vect n String) -> (typesStay : Vect n Ty) ->
                  snd (index x (typeNamesToContext (typesStay ++ typesSub) (namesStay ++ namesSub))) = ty ->
                  weakenN m y = x  ->
                  snd (index y (typeNamesToContext typesStay namesStay)) = ty
keepTypeMatches FZ FZ namesSub typesSub (name :: namesStay) (type :: typesStay) prf prf1 = prf
keepTypeMatches (FS x) FZ namesSub typesSub namesStay typesStay prf prf1 = absurd prf1
keepTypeMatches FZ (FS y) namesSub typesSub namesStay typesStay prf prf1 = absurd prf1
keepTypeMatches (FS x) (FS y) namesSub typesSub (name :: namesStay) (type :: typesStay) prf prf1 = keepTypeMatches x y namesSub typesSub namesStay typesStay prf (fsInjective prf1)

substituteTypeSame : {n : Nat} -> (x : Fin (n + m)) -> (y : Fin m) ->
                     (typesStay : Vect n Ty) -> (namesStay : Vect n String) -> 
                     (typesSub : Vect m Ty) -> (namesSub : Vect m String) -> 
                     (substitutions : HVect (map BigStepResult typesSub)) ->
                     (prf : snd (index x (typeNamesToContext (typesStay ++ typesSub) (namesStay ++ namesSub))) = ty) ->
                     (prfEq : shift n y = x) ->
                     BigStepResult ty = index y (map BigStepResult typesSub)
substituteTypeSame {n = 0} x y [] [] typesSub namesSub substitutions prf prfEq = rewrite prfEq in rewrite sym $ mapIndexCommutitive typesSub x BigStepResult in cong BigStepResult (typeNamesHelp prf)
substituteTypeSame {n = (S k)} FZ y typesStay namesStay typesSub namesSub substitutions prf prfEq = absurd prfEq
substituteTypeSame {n = (S k)} (FS x) y (type :: typesStay) (name :: namesStay) typesSub namesSub substitutions prf prfEq = substituteTypeSame x y typesStay namesStay typesSub namesSub substitutions prf (fsInjective prfEq)

weakenIndexNeutral : (x : Fin m) -> (context : Context m) -> snd (index x context) = ty -> {extra : Context n} -> snd (index (weakenN n x) (context ++ extra)) = ty
weakenIndexNeutral FZ (_ :: context) prf = prf
weakenIndexNeutral (FS x) (_ :: context) prf = weakenIndexNeutral x context prf

shift : {n,m : Nat} -> (extra : Context n) -> (context : Context m) -> (t : Term m ** HasType context t ty) -> (t : Term (m + n) ** HasType (context ++ extra) t ty)
shift extra context ((TmVar x) ** (VarHasType prf)) = (TmVar (weakenN n x) ** VarHasType (weakenIndexNeutral x context prf))
shift extra context ((TmAbs nm ty body) ** (AbsHasType bodyHasType)) = let (body' ** bodyHasType') = shift extra (addBinding context nm ty) (body ** bodyHasType) in
                                                                           (TmAbs nm ty body' ** AbsHasType bodyHasType')
shift extra context ((TmApp x y) ** (AppHasType xHasType yHasType)) = let (x' ** xHasType') = shift extra context (x ** xHasType)
                                                                          (y' ** yHasType') = shift extra context (y ** yHasType) in
                                                                          (TmApp x' y' ** AppHasType xHasType' yHasType')
shift extra context (TmTrue ** TrueHasType) = (TmTrue ** TrueHasType)
shift extra context (TmFalse ** FalseHasType) = (TmFalse ** FalseHasType)
shift extra context ((TmIf g t e) ** (IfHasType gHasType tHasType eHasType)) = let (g' ** gHasType') = shift extra context (g ** gHasType)
                                                                                   (t' ** tHasType') = shift extra context (t ** tHasType)
                                                                                   (e' ** eHasType') = shift extra context (e ** eHasType) in
                                                                                   (TmIf g' t' e' ** IfHasType gHasType' tHasType' eHasType')

substituteMany : {n,m : Nat} -> (t : Term (n + m)) -> (ty : Ty) -> 
                 (typesStay : Vect n Ty) -> (namesStay : Vect n String) -> 
                 (typesSub : Vect m Ty) -> (namesSub : Vect m String) -> 
                 (hasType : HasType (typeNamesToContext (typesStay ++ typesSub) (namesStay ++ namesSub)) t ty) ->
                 (substitutions : HVect (BigStepResult <$> typesSub)) ->
                 (tOut : Term n ** HasType (typeNamesToContext typesStay namesStay) tOut ty)
substituteMany (TmVar x) ty typesStay namesStay typesSub namesSub (VarHasType prf) substitutions = case splitSumID x of
                                                                                               (Left (y ** prfEq)) => (TmVar y ** VarHasType (keepTypeMatches x y namesSub typesSub namesStay typesStay prf prfEq))
                                                                                               (Right (y ** prfEq)) => let (val ** (_, hasType)) = valueOnly {ty} (rewrite substituteTypeSame x y typesStay namesStay typesSub namesSub substitutions prf prfEq in (index y substitutions)) in
                                                                                                                           shift (typeNamesToContext typesStay namesStay) [] (val ** hasType)
substituteMany (TmAbs nm tyIn body) (TyArr tyIn tyOut) typesStay namesStay typesSub namesSub (AbsHasType bodyHasType) substitutions = let (body' ** bodyHasType') = substituteMany body tyOut (tyIn :: typesStay) (nm :: namesStay) typesSub namesSub bodyHasType substitutions in
                                                                                                                                          (TmAbs nm tyIn body' ** AbsHasType bodyHasType')
substituteMany (TmApp x y) ty typesStay namesStay typesSub namesSub (AppHasType xHasType yHasType {varTy}) substitutions = let (x' ** xHasType') = substituteMany x (TyArr varTy ty) typesStay namesStay typesSub namesSub xHasType substitutions
                                                                                                                               (y' ** yHasType') = substituteMany y varTy typesStay namesStay typesSub namesSub yHasType substitutions in
                                                                                                                               (TmApp x' y' ** AppHasType xHasType' yHasType')
substituteMany TmTrue TyBool typesStay namesStay typesSub namesSub TrueHasType substitutions = (TmTrue ** TrueHasType)
substituteMany TmFalse TyBool typesStay namesStay typesSub namesSub FalseHasType substitutions = (TmFalse ** FalseHasType)
substituteMany (TmIf g t e) ty typesStay namesStay typesSub namesSub (IfHasType gHasType tHasType eHasType) substitutions = let (g' ** gHasType') = substituteMany g TyBool typesStay namesStay typesSub namesSub gHasType substitutions
                                                                                                                                (t' ** tHasType') = substituteMany t ty typesStay namesStay typesSub namesSub tHasType substitutions
                                                                                                                                (e' ** eHasType') = substituteMany e ty typesStay namesStay typesSub namesSub eHasType substitutions in
                                                                                                                                (TmIf g' t' e' ** IfHasType gHasType' tHasType' eHasType')

bigStepEvalGen : (n : Nat) -> (t : Term n) -> (tyOut : Ty) -> (types : Vect n Ty) -> (names : Vect n String) -> (hasType : HasType (typeNamesToContext types names) t tyOut) -> (substitutions : HVect (BigStepResult <$> types)) -> BigStepResult tyOut
bigStepEvalGen n (TmVar v) tyOut types names (VarHasType prf) substitutions = rewrite typeNamesHelp prf {v} {types} in rewrite mapIndexCommutitive types v BigStepResult in index v substitutions
bigStepEvalGen n (TmAbs name tyIn body) (TyArr tyIn tyOut) types names (AbsHasType bodyHasType) substitutions = let (body' ** bodyHasType') = substituteMany body tyOut [tyIn] [name] types names bodyHasType substitutions in
                                                                                                                    ((TmAbs name tyIn body' ** (AbsIsValue, AbsHasType bodyHasType')), (\arg => bigStepEvalGen (S n) body tyOut (tyIn :: types) (name :: names) bodyHasType (arg :: substitutions)))
bigStepEvalGen n (TmApp x y) tyOut types names (AppHasType xHasType yHasType {varTy}) substitutions = let (_, xf) = bigStepEvalGen n x (TyArr varTy tyOut) types names xHasType substitutions 
                                                                                                          y' = bigStepEvalGen n y varTy types names yHasType substitutions in
                                                                                                          xf y'
bigStepEvalGen n TmTrue TyBool types names TrueHasType substitutions = (TmTrue ** (TrueIsValue, TrueHasType))
bigStepEvalGen n TmFalse TyBool types names FalseHasType substitutions = (TmFalse ** (FalseIsValue, FalseHasType))
bigStepEvalGen n (TmIf g t e) tyOut types names (IfHasType gHasType tHasType eHasType) substitutions = case bigStepEvalGen n g TyBool types names gHasType substitutions of
                                                                                                            (TmTrue ** (isVal, hasType)) => bigStepEvalGen n t tyOut types names tHasType substitutions
                                                                                                            (TmFalse ** (isVal, hasType)) => bigStepEvalGen n e tyOut types names eHasType substitutions
                                                                                                            ((TmAbs nm ty body) ** (isVal, hasType)) => absurd hasType
                                                                                                            ((TmVar x) ** (isVal, hasType)) => absurd isVal
                                                                                                            ((TmApp x y) ** (isVal, hasType)) => absurd isVal
                                                                                                            ((TmIf x y z) ** (isVal, hasType)) => absurd isVal

bigStepEval : (t : Term 0) -> (ty : Ty) -> (hasType : HasType [] t ty) -> BigStepResult ty
bigStepEval t ty hasType = bigStepEvalGen 0 t ty [] [] hasType []

export
bigStepEvalTerm : (t : Term 0) -> {ty : Ty} -> (hasType : HasType [] t ty) -> Term 0
bigStepEvalTerm t hasType = fst $ valueOnly $ bigStepEval t ty hasType
