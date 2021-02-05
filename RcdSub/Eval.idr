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
import Data.DPair
import Data.Vect.Quantifiers
import Data.HVect

import Parser

%default total

mutual
  data RecordMapHasType : {n : Nat} -> Context n  -> RecordMap (Term n) -> RecordMap Ty -> Type where
    NilBindHasType : RecordMapHasType context (MkRecordMap EmptySet []) (MkRecordMap EmptySet [])
    ConsBindHasType : (headHasType : HasType context term ty) -> (tailHasType : RecordMapHasType context (MkRecordMap keysTail termsTail) (MkRecordMap keysTail typesTail)) -> RecordMapHasType context (MkRecordMap (AddElement name keysTail nameIsNew) (term :: termsTail)) (MkRecordMap (AddElement name keysTail nameIsNew) (ty :: typesTail))

  data HasType : {n : Nat} -> Context n -> Term n -> Ty -> Type where
    VarHasType : getBindingType context v = type -> HasType context (TmVar v) type
    AbsHasType : (bodyHasType : HasType (addBinding context name varTy) body type) -> HasType context (TmAbs name varTy body) (TyArr varTy type)
    AppHasType : {varTy : Ty} -> (xHasType : HasType context x (TyArr varTy returnTy)) -> (yHasType : HasType context y varTy) -> HasType context (TmApp x y) returnTy
    RecHasType : RecordMapHasType context recBinds tyBinds -> HasType context (TmRec recBinds) (TyRec tyBinds)
    ProjHasType : (i : Nat) -> (names : BindingKeys) -> (types : Vect (length names) Ty) -> HasType context rec (TyRec (MkRecordMap names types)) -> {auto 0 ok : InBounds i names} -> HasType context (TmProj rec (index i names)) (index (inBoundsToFinLength i {ok}) types)

withProof : (x : t) -> (y : t ** x = y)
withProof x = (x ** Refl)

mutual
  getRecTypes : {n : Nat} -> (context : Context n) -> (names : BindingKeys) -> (terms : Vect (length names) (Term n)) -> Either String (tyRec : RecordMap Ty ** (RecordMapHasType context (MkRecordMap names terms) tyRec))
  getRecTypes context EmptySet [] = Right (MkRecordMap EmptySet [] ** NilBindHasType)
  getRecTypes context (AddElement name names nameIsNew) (term :: terms) = do (ty ** hasType) <- getType context term
                                                                             (MkRecordMap names' types ** recHasType) <- getRecTypes context names terms
                                                                             Right $ case recHasType of
                                                                                          NilBindHasType => (MkRecordMap (AddElement name names nameIsNew) [ty] ** ConsBindHasType hasType NilBindHasType)
                                                                                          (ConsBindHasType headHasType tailHasType) => (MkRecordMap (AddElement name names nameIsNew) (ty :: types) ** ConsBindHasType hasType (ConsBindHasType headHasType tailHasType))

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
  getType context (TmRec (MkRecordMap names terms)) = do (tyRec ** recHasType) <- getRecTypes context names terms
                                                         Right (TyRec tyRec ** RecHasType recHasType)
  getType context (TmProj rec name) = do (TyRec (MkRecordMap names types) ** recHasType) <- getType context rec
                                          | _ => Left "Expected record type in projection"
                                         case getIndex name names of
                                              Nothing => Left (name ++ " is not a label in record")
                                              (Just (n ** inBounds ** isIndex)) => Right (index (inBoundsToFinLength n) types ** rewrite isIndex in ProjHasType n names types recHasType)

data IsValue : Term n -> Type where
  AbsIsValue : IsValue (TmAbs name ty body)
  RecIsValue : {0 names : BindingKeys} -> {0 recTerms : Vect (length names) (Term n)} -> All IsValue recTerms -> IsValue (TmRec (MkRecordMap names recTerms))

{-
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

Sized (HasType context t ty) where
  size (VarHasType prf) = 1
  size (AbsHasType bodyHasType) = S (size bodyHasType)
  size (AppHasType x y) = (size x) + (size y)
  size TrueHasType = 1
  size FalseHasType = 1
  size (IfHasType g t e) = (size g) + (size t) + (size e)
                                  -}

mutual
  BigStepResults : (Vect n Ty) -> Vect n Type
  BigStepResults [] = []
  BigStepResults (ty :: tys) = BigStepResult ty :: BigStepResults tys

  BigStepResult : (ty : Ty) -> Type
  BigStepResult (TyRec (MkRecordMap names types)) = HVect (BigStepResults types)
  BigStepResult (TyArr tyIn tyOut) = ((t : Term 0 ** (IsValue t, HasType [] t (TyArr tyIn tyOut))), (BigStepResult tyIn) -> (BigStepResult tyOut))

mutual
  recValueOnly : (names : BindingKeys) -> (types : Vect (length names) Ty) -> HVect (BigStepResults types) -> (t : Term 0 ** (IsValue t, HasType [] t (TyRec (MkRecordMap names types))))
  recValueOnly EmptySet [] [] = (TmRec (MkRecordMap EmptySet []) ** (RecIsValue [], RecHasType NilBindHasType))
  recValueOnly (AddElement name names nameIsNew) (ty :: tys) (stepResult :: stepResults) =
    let (tHead ** (headIsVal, headIsType)) = valueOnly stepResult in
        case recValueOnly names tys stepResults of
             ((TmAbs name ty body) ** (AbsIsValue, absIsType)) impossible
             ((TmRec (MkRecordMap EmptySet [])) ** ((RecIsValue []), (RecHasType NilBindHasType))) => (TmRec (MkRecordMap (AddElement name names nameIsNew) [tHead]) ** (RecIsValue [headIsVal], RecHasType (ConsBindHasType headIsType NilBindHasType)))
             ((TmRec (MkRecordMap (AddElement name' names' nameIsNew') (term :: termsTail))) ** ((RecIsValue allIsValue), (RecHasType (ConsBindHasType headHasType tailHasType)))) => (TmRec (MkRecordMap (AddElement name names nameIsNew) (tHead :: term :: termsTail)) ** (RecIsValue (headIsVal :: allIsValue), RecHasType (ConsBindHasType headIsType (ConsBindHasType headHasType tailHasType))))

  valueOnly : {ty : Ty} -> BigStepResult ty -> (t : Term 0 ** (IsValue t, HasType [] t ty))
  valueOnly {ty = (TyRec (MkRecordMap names types))} stepResults = recValueOnly names types stepResults
  valueOnly {ty = (TyArr _ _)} (val, _) = val

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
                     (prf : snd (index x (typeNamesToContext (typesStay ++ typesSub) (namesStay ++ namesSub))) = ty) ->
                     (prfEq : shift n y = x) ->
                     BigStepResult ty = index y (map BigStepResult typesSub)
substituteTypeSame {n = 0} x y [] [] typesSub namesSub prf prfEq = rewrite prfEq in rewrite sym $ mapIndexCommutitive typesSub x BigStepResult in cong BigStepResult (typeNamesHelp prf)
substituteTypeSame {n = (S k)} FZ y typesStay namesStay typesSub namesSub prf prfEq = absurd prfEq
substituteTypeSame {n = (S k)} (FS x) y (type :: typesStay) (name :: namesStay) typesSub namesSub prf prfEq = substituteTypeSame x y typesStay namesStay typesSub namesSub prf (fsInjective prfEq)

weakenIndexNeutral : (x : Fin m) -> (context : Context m) -> snd (index x context) = ty -> {extra : Context n} -> snd (index (weakenN n x) (context ++ extra)) = ty
weakenIndexNeutral FZ (_ :: context) prf = prf
weakenIndexNeutral (FS x) (_ :: context) prf = weakenIndexNeutral x context prf

mutual
  shiftRec : {n, m : Nat} -> (extra : Context n) -> (context : Context m) -> (names : BindingKeys) -> (terms : Vect (length names) (Term m)) -> (recHasType : RecordMapHasType context (MkRecordMap names terms) recTy) -> (rec : RecordMap (Term (m + n)) ** RecordMapHasType (context ++ extra) rec recTy)
  shiftRec extra context EmptySet [] NilBindHasType = (MkRecordMap EmptySet [] ** NilBindHasType)
  shiftRec extra context (AddElement newVal set valIsNew) (term :: terms) (ConsBindHasType headHasType tailHasType) = let ((MkRecordMap keys values) ** recHasType) = shiftRec extra context set terms tailHasType
                                                                                                                          (term' ** headHasType') = shift extra context (term ** headHasType) in
                                                                                                                          case recHasType of
                                                                                                                               NilBindHasType => (MkRecordMap (AddElement newVal set valIsNew) [term'] ** ConsBindHasType headHasType' NilBindHasType)
                                                                                                                               (ConsBindHasType x y) => (MkRecordMap (AddElement newVal set valIsNew) (term' :: values) ** ConsBindHasType headHasType' (ConsBindHasType x y))

  shift : {n,m : Nat} -> (extra : Context n) -> (context : Context m) -> (t : Term m ** HasType context t ty) -> (t : Term (m + n) ** HasType (context ++ extra) t ty)
  shift extra context ((TmVar x) ** (VarHasType prf)) = (TmVar (weakenN n x) ** VarHasType (weakenIndexNeutral x context prf))
  shift extra context ((TmAbs nm ty body) ** (AbsHasType bodyHasType)) = let (body' ** bodyHasType') = shift extra (addBinding context nm ty) (body ** bodyHasType) in
                                                                             (TmAbs nm ty body' ** AbsHasType bodyHasType')
  shift extra context ((TmApp x y) ** (AppHasType xHasType yHasType)) = let (x' ** xHasType') = shift extra context (x ** xHasType)
                                                                            (y' ** yHasType') = shift extra context (y ** yHasType) in
                                                                            (TmApp x' y' ** AppHasType xHasType' yHasType')
  shift extra context ((TmRec (MkRecordMap names terms)) ** (RecHasType recHasType)) = let (rec' ** recHasType') = shiftRec extra context names terms recHasType in
                                                                                           (TmRec rec' ** RecHasType recHasType')
  shift extra context ((TmProj rec _) ** (ProjHasType i names types recHasType)) = let (rec' ** recHasType') = shift extra context (rec ** recHasType) in
                                                                                      (TmProj rec' (index i names) ** (ProjHasType i names types recHasType'))

mutual

  substituteManyRec : {n,m : Nat} -> (rec : RecordMap (Term (n + m))) -> (tyRec : RecordMap Ty) -> 
                      (typesStay : Vect n Ty) -> (namesStay : Vect n String) -> 
                      (typesSub : Vect m Ty) -> (namesSub : Vect m String) -> 
                      (hasType : RecordMapHasType (typeNamesToContext (typesStay ++ typesSub) (namesStay ++ namesSub)) rec tyRec) ->
                      (substitutions : HVect (BigStepResult <$> typesSub)) ->
                      (recOut : RecordMap (Term n) ** RecordMapHasType (typeNamesToContext typesStay namesStay) recOut tyRec)
  substituteManyRec (MkRecordMap EmptySet []) (MkRecordMap EmptySet []) typesStay namesStay typesSub namesSub NilBindHasType substitutions = (MkRecordMap EmptySet [] **  NilBindHasType)
  substituteManyRec (MkRecordMap (AddElement name names nameIsNew) (term :: termsTail)) (MkRecordMap (AddElement name names nameIsNew) (ty :: typesTail)) typesStay namesStay typesSub namesSub (ConsBindHasType headHasType tailHasType) substitutions = 
    let (terms' ** termsHasType) = substituteManyRec' (AddElement name names nameIsNew) (term :: termsTail) (ty :: typesTail) typesStay namesStay typesSub namesSub (ConsBindHasType headHasType tailHasType) substitutions in
        (MkRecordMap (AddElement name names nameIsNew) terms' ** termsHasType)
    where
      substituteManyRec' : {n,m : Nat} -> (names : BindingKeys) -> (terms : Vect (length names) (Term (n + m))) -> (types : Vect (length names) Ty) -> 
                           (typesStay : Vect n Ty) -> (namesStay : Vect n String) -> 
                           (typesSub : Vect m Ty) -> (namesSub : Vect m String) -> 
                           (hasType : RecordMapHasType (typeNamesToContext (typesStay ++ typesSub) (namesStay ++ namesSub)) (MkRecordMap names terms) (MkRecordMap names types)) ->
                           (substitutions : HVect (BigStepResult <$> typesSub)) ->
                           (termsOut : Vect (length names) (Term n) ** RecordMapHasType (typeNamesToContext typesStay namesStay) (MkRecordMap names termsOut) (MkRecordMap names types))
      substituteManyRec' EmptySet [] [] typesStay namesStay typesSub namesSub NilBindHasType substitutions = ([] **  NilBindHasType)
      substituteManyRec' (AddElement name names nameIsNew) (term :: termsTail) (ty :: typesTail) typesStay namesStay typesSub namesSub (ConsBindHasType headHasType tailHasType) substitutions = 
        let (term' ** headHasType') = substituteMany term ty typesStay namesStay typesSub namesSub headHasType substitutions
            (termsTail' ** tailHasType') = substituteManyRec' names termsTail typesTail typesStay namesStay typesSub namesSub tailHasType substitutions in
            ((term' :: termsTail') ** ConsBindHasType headHasType' tailHasType')

  substituteMany : {n,m : Nat} -> (t : Term (n + m)) -> (ty : Ty) -> 
                   (typesStay : Vect n Ty) -> (namesStay : Vect n String) -> 
                   (typesSub : Vect m Ty) -> (namesSub : Vect m String) -> 
                   (hasType : HasType (typeNamesToContext (typesStay ++ typesSub) (namesStay ++ namesSub)) t ty) ->
                   (substitutions : HVect (BigStepResult <$> typesSub)) ->
                   (tOut : Term n ** HasType (typeNamesToContext typesStay namesStay) tOut ty)
  substituteMany (TmVar x) ty typesStay namesStay typesSub namesSub (VarHasType prf) substitutions = case splitSumID x of
                                                                                                 (Left (y ** prfEq)) => (TmVar y ** VarHasType (keepTypeMatches x y namesSub typesSub namesStay typesStay prf prfEq))
                                                                                                 (Right (y ** prfEq)) => let (val ** (_, hasType)) = valueOnly {ty} (rewrite substituteTypeSame x y typesStay namesStay typesSub namesSub prf prfEq in (index y substitutions)) in
                                                                                                                             shift (typeNamesToContext typesStay namesStay) [] (val ** hasType)
  substituteMany (TmAbs nm tyIn body) (TyArr tyIn tyOut) typesStay namesStay typesSub namesSub (AbsHasType bodyHasType) substitutions = let (body' ** bodyHasType') = substituteMany body tyOut (tyIn :: typesStay) (nm :: namesStay) typesSub namesSub bodyHasType substitutions in
                                                                                                                                            (TmAbs nm tyIn body' ** AbsHasType bodyHasType')
  substituteMany (TmApp x y) ty typesStay namesStay typesSub namesSub (AppHasType xHasType yHasType {varTy}) substitutions = let (x' ** xHasType') = substituteMany x (TyArr varTy ty) typesStay namesStay typesSub namesSub xHasType substitutions
                                                                                                                                 (y' ** yHasType') = substituteMany y varTy typesStay namesStay typesSub namesSub yHasType substitutions in
                                                                                                                                 (TmApp x' y' ** AppHasType xHasType' yHasType')
  substituteMany (TmRec rec) (TyRec tyRec) typesStay namesStay typesSub namesSub (RecHasType recHasTy) substitutions = let (rec' ** recHasType') = substituteManyRec rec tyRec typesStay namesStay typesSub namesSub recHasTy substitutions in
                                                                                                                           (TmRec rec' ** RecHasType recHasType')
  substituteMany (TmProj rec _) _ typesStay namesStay typesSub namesSub (ProjHasType i names types recHasTy) substitutions = let (rec' ** recHasType') = substituteMany rec _ typesStay namesStay typesSub namesSub recHasTy substitutions in
                                                                                                                                 (TmProj rec' (index i names) ** ProjHasType i names types recHasType')

indexBigStepResultsIsBigStepIndex : (i : Fin n) -> (tyRec : Vect n Ty) -> BigStepResult (index i tyRec) = index i (BigStepResults tyRec)
indexBigStepResultsIsBigStepIndex FZ (ty :: _) = Refl
indexBigStepResultsIsBigStepIndex (FS i) (_ :: tyRec) = indexBigStepResultsIsBigStepIndex i tyRec

mutual
  bigStepEvalGenRec' : (n : Nat) -> (recNames : BindingKeys) -> (terms : Vect (length recNames) (Term n)) -> (recTypes : Vect (length recNames) Ty) -> 
                       (types : Vect n Ty) -> (names : Vect n String) -> (hasType : RecordMapHasType (typeNamesToContext types names) (MkRecordMap recNames terms) (MkRecordMap recNames recTypes)) -> 
                       (substitutions : HVect (BigStepResult <$> types)) -> BigStepResult (TyRec (MkRecordMap recNames recTypes))
  bigStepEvalGenRec' n EmptySet [] [] types names hasType substitutions = []
  bigStepEvalGenRec' n (AddElement name recNames nameIsNew) (term :: terms) (ty :: recTypes) types names (ConsBindHasType headHasType tailHasType) substitutions = 
    let headResult = bigStepEvalGen n term ty types names headHasType substitutions
        tailResult = bigStepEvalGenRec' n recNames terms recTypes types names tailHasType substitutions in
        headResult :: tailResult

  bigStepEvalGenRec : (n : Nat) -> (rec : RecordMap (Term n)) -> (tyRec : RecordMap Ty) -> (types : Vect n Ty) -> (names : Vect n String) -> (hasType : RecordMapHasType (typeNamesToContext types names) rec tyRec) -> (substitutions : HVect (BigStepResult <$> types)) -> BigStepResult (TyRec tyRec)
  bigStepEvalGenRec n (MkRecordMap EmptySet []) (MkRecordMap EmptySet []) types names NilBindHasType substitutions = []
  bigStepEvalGenRec n (MkRecordMap (AddElement name recNames nameIsNew) (term :: termsTail)) (MkRecordMap (AddElement name recNames nameIsNew) (ty :: typesTail)) types names (ConsBindHasType headHasType tailHasType) substitutions = 
    bigStepEvalGenRec' n (AddElement name recNames nameIsNew) (term :: termsTail) (ty :: typesTail) types names (ConsBindHasType headHasType tailHasType) substitutions

  bigStepEvalGen : (n : Nat) -> (t : Term n) -> (tyOut : Ty) -> (types : Vect n Ty) -> (names : Vect n String) -> (hasType : HasType (typeNamesToContext types names) t tyOut) -> (substitutions : HVect (BigStepResult <$> types)) -> BigStepResult tyOut
  bigStepEvalGen n (TmVar v) tyOut types names (VarHasType prf) substitutions = rewrite typeNamesHelp prf {v} {types} in rewrite mapIndexCommutitive types v BigStepResult in index v substitutions
  bigStepEvalGen n (TmAbs name tyIn body) (TyArr tyIn tyOut) types names (AbsHasType bodyHasType) substitutions = let (body' ** bodyHasType') = substituteMany body tyOut [tyIn] [name] types names bodyHasType substitutions in
                                                                                                                      ((TmAbs name tyIn body' ** (AbsIsValue, AbsHasType bodyHasType')), (\arg => bigStepEvalGen (S n) body tyOut (tyIn :: types) (name :: names) bodyHasType (arg :: substitutions)))
  bigStepEvalGen n (TmApp x y) tyOut types names (AppHasType xHasType yHasType {varTy}) substitutions = let (_, xf) = bigStepEvalGen n x (TyArr varTy tyOut) types names xHasType substitutions 
                                                                                                            y' = bigStepEvalGen n y varTy types names yHasType substitutions in
                                                                                                            xf y'
  bigStepEvalGen n (TmRec rec) (TyRec tyRec) types names (RecHasType recHasType) substitutions = bigStepEvalGenRec n rec tyRec types names recHasType substitutions
  bigStepEvalGen n (TmProj rec _) _ types names (ProjHasType i recNames tyRec recHasType {ok}) substitutions = let recResult = bigStepEvalGen n rec (TyRec (MkRecordMap recNames tyRec)) types names recHasType substitutions in
                                                                                                                   rewrite indexBigStepResultsIsBigStepIndex (inBoundsToFinLength i {ok}) tyRec in  index (inBoundsToFinLength i) recResult

bigStepEval : (t : Term 0) -> (ty : Ty) -> (hasType : HasType [] t ty) -> BigStepResult ty
bigStepEval t ty hasType = bigStepEvalGen 0 t ty [] [] hasType []

export
bigStepEvalTerm : (t : Term 0) -> {ty : Ty} -> (hasType : HasType [] t ty) -> Term 0
bigStepEvalTerm t hasType = fst $ valueOnly $ bigStepEval t ty hasType
