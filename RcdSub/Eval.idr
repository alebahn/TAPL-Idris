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

import Terms

%default total

data SubSet : BindingKeys -> BindingKeys -> Type where
  EmptySubSet : SubSet EmptySet x
  AddToSubSet : SubSet a b -> {0 ok : InBounds i b} -> (newNotInA : SetMissing (index i b {ok}) a) -> SubSet (AddElement (index i b {ok}) a newNotInA) b

mutual
  data RecSub : (RecordMap Ty) -> (RecordMap Ty) -> Type where
    RecSubEmpty : RecSub x (MkRecordMap EmptySet [])
    RecSubAdd : {0 namesA, namesB : BindingKeys} -> {0 typesA : Vect (length namesA) Ty} -> {0 typesB : Vect (length namesB) Ty} -> {i : Nat} -> {typeB : Ty} -> {0 ok : InBounds i namesA} -> {0 newNotInB : SetMissing (index i namesA) namesB} ->
                RecSub (MkRecordMap namesA typesA) (MkRecordMap namesB typesB) -> Subtype (index (inBoundsToFinLength i {ok}) typesA) typeB -> RecSub (MkRecordMap namesA typesA) (MkRecordMap (AddElement (index i namesA {ok}) namesB newNotInB) (typeB :: typesB))

  data Subtype : Ty -> Ty -> Type where
    SubTop : Subtype a TyTop
    SubArrow : Subtype inB inA -> Subtype outA outB -> Subtype (TyArr inA outA) (TyArr inB outB)
    SubRcd : RecSub recA recB -> Subtype (TyRec recA) (TyRec recB)

Uninhabited (Subtype (TyArr a b) (TyRec rec)) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible

Uninhabited (Subtype (TyRec rec) (TyArr a b)) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible

Uninhabited (Subtype TyTop (TyArr a b)) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible

Uninhabited (Subtype TyTop (TyRec rec)) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible

recSubAddLeft : RecSub (MkRecordMap namesA typesA) b -> RecSub (MkRecordMap (AddElement nameA namesA nameANotInNamesA) (tyA :: typesA)) b
recSubAddLeft RecSubEmpty = RecSubEmpty
recSubAddLeft (RecSubAdd aRecSubB tyASubTyB {ok} {i} {typeB}) = rewrite succIndexOfAddElementEq i {ok} in RecSubAdd (recSubAddLeft aRecSubB) (replace (succIndexOfConsEq i) {p=(\x => Subtype x typeB)} tyASubTyB) {ok=succInbounds ok}

recSubDepth :  (names : BindingKeys) -> (typesA, typesB : Vect (length names) Ty) -> (allTypesSub : HVect (zipWith Subtype typesA typesB)) -> RecSub (MkRecordMap names typesA) (MkRecordMap names typesB)
recSubDepth EmptySet [] [] [] = RecSubEmpty
recSubDepth (AddElement name names nameIsNew) (typeA :: typesA) (typeB :: typesB) (sub :: subs) =
  let tailSub = recSubDepth names typesA typesB subs in
      RecSubAdd (recSubAddLeft tailSub) sub {i=0} {ok=InFirst}

mutual
  recSubRefl : {x : RecordMap Ty} -> RecSub x x
  recSubRefl {x = (MkRecordMap keys values)} = recSubRefl' keys values
    where
      recSubRefl' : (names : BindingKeys) -> (types : Vect (length names) Ty) -> RecSub (MkRecordMap names types) (MkRecordMap names types)
      recSubRefl' EmptySet [] = RecSubEmpty
      recSubRefl' (AddElement name names nameIsNew) (ty :: types) = let baseRefl = recSubRefl' names types
                                                                        addOnLeft = recSubAddLeft baseRefl in
                                                                        RecSubAdd {i=0} {ok=InFirst} addOnLeft subRefl

  subRefl : {x : Ty} -> Subtype x x
  subRefl {x = (TyRec x)} = SubRcd recSubRefl
  subRefl {x = (TyArr x y)} = SubArrow subRefl subRefl
  subRefl {x = TyTop} = SubTop

record RecSubDatum (namesX, namesY : BindingKeys) (typesX : Vect (length namesX) Ty) (typesY : Vect (length namesY) Ty) (iY : Nat) (0 inBoundsY : InBounds iY namesY) where
  constructor MkRecSubDatum
  iX : Nat
  0 inBoundsX : InBounds iX namesX
  subType : Subtype (index (inBoundsToFinLength iX {ok=inBoundsX}) typesX) (index (inBoundsToFinLength iY {ok=inBoundsY}) typesY)
  namesSame : index iY namesY = index iX namesX

datumCons : RecSubDatum namesX namesY typesX typesY iY inBoundsY -> RecSubDatum namesX (AddElement name namesY nameIsNew) typesX (type :: typesY) (S iY) (InLater inBoundsY)
datumCons (MkRecSubDatum iX inBoundsX subType namesSame) = MkRecSubDatum iX inBoundsX subType namesSame

indexSubType : RecSub (MkRecordMap namesX typesX) (MkRecordMap namesY typesY) -> (i : Nat) -> {0 ok : InBounds i namesY}  -> RecSubDatum namesX namesY typesX typesY i ok
indexSubType (RecSubAdd _ subTy {i=iX} {ok=okX}) 0 {ok = InFirst} = MkRecSubDatum iX okX subTy Refl
indexSubType (RecSubAdd recSub _) (S k) {ok = InLater ok} = datumCons (indexSubType recSub k {ok})

mutual
  subRecTrans :  RecSub x y -> RecSub y z -> RecSub x z
  subRecTrans _ RecSubEmpty = RecSubEmpty
  subRecTrans RecSubEmpty (RecSubAdd v s {ok}) = absurd ok
  subRecTrans recSubX@(RecSubAdd _ subX) (RecSubAdd recSubY subY {i=iy} {ok=okY}) = let indexDatum = indexSubType recSubX iy {ok=okY}
                                                                                        transRest = subRecTrans recSubX recSubY in
                                                                                        rewrite indexDatum.namesSame in RecSubAdd transRest (subTrans indexDatum.subType subY) {i=indexDatum.iX} {ok=indexDatum.inBoundsX}

  subTrans : Subtype x y -> Subtype y z -> Subtype x z
  subTrans _ SubTop = SubTop
  subTrans (SubArrow insX outsX) (SubArrow insY outsY) = SubArrow (subTrans insY insX) (subTrans outsX outsY)
  subTrans (SubRcd x) (SubRcd y) = SubRcd (subRecTrans x y)

partial
setMissingNotSubset : SetMissing nameY namesX -> Not (RecSub (MkRecordMap namesX typesX) (MkRecordMap (AddElement nameY namesY nameYNotInNamesY) (tyY :: typesY)))
setMissingNotSubset setMissing (RecSubAdd _ _ {i} {ok}) = void $ setMissingIndexAbsurd namesX i setMissing

mutual
  decRecSub' : (namesX : BindingKeys) -> (typesX : Vect (length namesX) Ty) -> (namesY : BindingKeys) -> (typesY : Vect (length namesY) Ty) -> Dec (RecSub (MkRecordMap namesX typesX) (MkRecordMap namesY typesY))
  decRecSub' namesX typesX EmptySet [] = Yes RecSubEmpty
  decRecSub' namesX typesX (AddElement name namesY nameIsNew) (ty :: typesY) =
    case getIndex name namesX of
         (Left notInSet) => No (setMissingNotSubset notInSet)
         (Right (i ** inBounds ** isIndexOf)) =>
                case decSubtype (index (inBoundsToFinLength i {ok = inBounds}) typesX) ty of
                     (No contra) => No (\(RecSubAdd _ isSub {i=i'} {ok}) => contra $ rewrite indexSameToInBoundsSame namesX i i' (sym isIndexOf) {ok=inBounds} {ok'=ok} in isSub)
                     (Yes headIsSub) => case decRecSub' namesX typesX namesY typesY of
                                       (Yes tailIsSub) => Yes (rewrite isIndexOf in RecSubAdd tailIsSub headIsSub)
                                       (No contra) => No (\(RecSubAdd recIsSub _ {i=i'} {ok}) => contra recIsSub)

  decRecSub : (x, y : RecordMap Ty) -> Dec (RecSub x y)
  decRecSub (MkRecordMap namesX typesX) (MkRecordMap namesY typesY) = decRecSub' namesX typesX namesY typesY

  decSubtype : (x, y : Ty) -> Dec (Subtype x y)
  decSubtype _ TyTop = Yes SubTop
  decSubtype (TyRec x) (TyRec y) with (decRecSub x y)
    decSubtype (TyRec _) (TyRec _) | (Yes prf) = Yes (SubRcd prf)
    decSubtype (TyRec x) (TyRec y) | (No contra) = No (\(SubRcd prf) => contra prf)
  decSubtype (TyArr x w) (TyArr y z) with (decSubtype y x)
    decSubtype (TyArr x w) (TyArr y z) | (No insNotSub) = No (\(SubArrow insSub _) => insNotSub insSub)
    decSubtype (TyArr x w) (TyArr y z) | (Yes insSub) with (decSubtype w z)
      decSubtype (TyArr x w) (TyArr y z) | (Yes insSub) | (Yes outsSub) = Yes (SubArrow insSub outsSub)
      decSubtype (TyArr x w) (TyArr y z) | (Yes insSub) | (No outsNotSub) = No (\(SubArrow _ outsSub) => outsNotSub outsSub)
  decSubtype (TyArr x z) (TyRec y) = No uninhabited
  decSubtype TyTop (TyRec y) = No uninhabited
  decSubtype (TyRec x) (TyArr y z) = No uninhabited
  decSubtype TyTop (TyArr y z) = No uninhabited

mutual
  data RecordMapHasType : {n : Nat} -> Context n  -> RecordMap (Term n) -> RecordMap Ty -> Type where
    NilBindHasType : RecordMapHasType context (MkRecordMap EmptySet []) (MkRecordMap EmptySet [])
    ConsBindHasType : (headHasType : HasType context term ty) -> (tailHasType : RecordMapHasType context (MkRecordMap keysTail termsTail) (MkRecordMap keysTail typesTail)) -> RecordMapHasType context (MkRecordMap (AddElement name keysTail nameIsNew) (term :: termsTail)) (MkRecordMap (AddElement name keysTail nameIsNew) (ty :: typesTail))

  data HasType : {n : Nat} -> Context n -> Term n -> Ty -> Type where
    VarHasType : getBindingType context v = type -> HasType context (TmVar v) type
    AbsHasType : (bodyHasType : HasType (addBinding context name varTy) body type) -> HasType context (TmAbs name varTy body) (TyArr varTy type)
    AppHasType : {varTy,varSubTy : Ty} -> (xHasType : HasType context x (TyArr varTy returnTy)) -> (isSub : Subtype varSubTy varTy) -> (yHasType : HasType context y varSubTy) -> HasType context (TmApp x y) returnTy
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
                                   case decSubtype subTy var of
                                        (Yes subType) => Right (return ** (AppHasType funcHasType subType subHasType))
                                        (No _) => Left "Type passed to application is not a subtype of argument to function"
  getType context (TmRec (MkRecordMap names terms)) = do (tyRec ** recHasType) <- getRecTypes context names terms
                                                         Right (TyRec tyRec ** RecHasType recHasType)
  getType context (TmProj rec name) = do (TyRec (MkRecordMap names types) ** recHasType) <- getType context rec
                                          | _ => Left "Expected record type in projection"
                                         case getIndex name names of
                                              Left _ => Left (name ++ " is not a label in record")
                                              (Right (n ** inBounds ** isIndex)) => Right (index (inBoundsToFinLength n) types ** rewrite isIndex in ProjHasType n names types recHasType)

data IsValue : Term n -> Type where
  AbsIsValue : IsValue (TmAbs name ty body)
  RecIsValue : {0 names : BindingKeys} -> {0 recTerms : Vect (length names) (Term n)} -> All IsValue recTerms -> IsValue (TmRec (MkRecordMap names recTerms))

CoreValue : (ty : Ty) -> Type
CoreValue ty = (t : Term 0 ** isValue : IsValue t ** subTy : Ty ** isSubtype : Subtype subTy ty ** HasType [] t subTy)

mutual
  BigStepResults : (Vect n Ty) -> Vect n Type
  BigStepResults [] = []
  BigStepResults (ty :: tys) = BigStepResult ty :: BigStepResults tys

  BigStepResult : (ty : Ty) -> Type
  BigStepResult TyTop = CoreValue TyTop
  BigStepResult (TyRec (MkRecordMap names types)) = (CoreValue (TyRec (MkRecordMap names types)), HVect (BigStepResults types))
  BigStepResult (TyArr tyIn tyOut) = (CoreValue (TyArr tyIn tyOut), (BigStepResult tyIn) -> (BigStepResult tyOut))

valueOnly : {ty : Ty} -> BigStepResult ty -> CoreValue ty
valueOnly {ty = TyTop} x = x
valueOnly {ty = TyRec (MkRecordMap _ _)} (x, _) = x
valueOnly {ty = TyArr _ _} (x, _) = x

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
  shift extra context ((TmApp x y) ** (AppHasType xHasType argIsSubType yHasType)) = let (x' ** xHasType') = shift extra context (x ** xHasType)
                                                                                         (y' ** yHasType') = shift extra context (y ** yHasType) in
                                                                                         (TmApp x' y' ** AppHasType xHasType' argIsSubType yHasType')
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
                      (recOut : RecordMap (Term n) ** subtyRec : RecordMap Ty ** isSubType : RecSub subtyRec tyRec ** RecordMapHasType (typeNamesToContext typesStay namesStay) recOut subtyRec)
  substituteManyRec (MkRecordMap EmptySet []) (MkRecordMap EmptySet []) typesStay namesStay typesSub namesSub NilBindHasType substitutions = (MkRecordMap EmptySet [] ** MkRecordMap EmptySet [] ** RecSubEmpty ** NilBindHasType)
  substituteManyRec (MkRecordMap (AddElement name names nameIsNew) (term :: termsTail)) (MkRecordMap (AddElement name names nameIsNew) (ty :: typesTail)) typesStay namesStay typesSub namesSub (ConsBindHasType headHasType tailHasType) substitutions =
    let (terms ** subtypes ** isSubType ** hasType) = substituteManyRec' (AddElement name names nameIsNew) (term :: termsTail) (ty :: typesTail) typesStay namesStay typesSub namesSub (ConsBindHasType headHasType tailHasType) substitutions in
        (MkRecordMap (AddElement name names nameIsNew) terms ** MkRecordMap (AddElement name names nameIsNew) subtypes ** isSubType ** hasType)
   where
      substituteManyRec' : {n,m : Nat} -> (names : BindingKeys) -> (terms : Vect (length names) (Term (n + m))) -> (types : Vect (length names) Ty) ->
                           (typesStay : Vect n Ty) -> (namesStay : Vect n String) ->
                           (typesSub : Vect m Ty) -> (namesSub : Vect m String) ->
                           (hasType : RecordMapHasType (typeNamesToContext (typesStay ++ typesSub) (namesStay ++ namesSub)) (MkRecordMap names terms) (MkRecordMap names types)) ->
                           (substitutions : HVect (BigStepResult <$> typesSub)) ->
                           (termsOut : Vect (length names) (Term n) ** subtypesOut : Vect (length names) Ty ** isSubType : RecSub (MkRecordMap names subtypesOut) (MkRecordMap names types) ** RecordMapHasType (typeNamesToContext typesStay namesStay) (MkRecordMap names termsOut) (MkRecordMap names subtypesOut))
      substituteManyRec' EmptySet [] [] typesStay namesStay typesSub namesSub NilBindHasType substitutions = ([] ** [] ** RecSubEmpty ** NilBindHasType)
      substituteManyRec' (AddElement name names nameIsNew) (term :: termsTail) (ty :: typesTail) typesStay namesStay typesSub namesSub (ConsBindHasType headHasType tailHasType) substitutions =
        let (term' ** subty ** isSubty ** hasSubty) = substituteMany term ty typesStay namesStay typesSub namesSub headHasType substitutions
            (terms' ** subtypes ** areSubTypes ** haveSubtypes) = substituteManyRec' names termsTail typesTail typesStay namesStay typesSub namesSub tailHasType substitutions in
            (term' :: terms' ** subty :: subtypes ** RecSubAdd (recSubAddLeft areSubTypes) isSubty {i=0} {ok=InFirst} ** ConsBindHasType hasSubty haveSubtypes)

  substituteMany : {n,m : Nat} -> (t : Term (n + m)) -> (ty : Ty) ->
                   (typesStay : Vect n Ty) -> (namesStay : Vect n String) ->
                   (typesSub : Vect m Ty) -> (namesSub : Vect m String) ->
                   (hasType : HasType (typeNamesToContext (typesStay ++ typesSub) (namesStay ++ namesSub)) t ty) ->
                   (substitutions : HVect (BigStepResult <$> typesSub)) ->
                   (tOut : Term n ** subTy : Ty ** isSubType : Subtype subTy ty ** HasType (typeNamesToContext typesStay namesStay) tOut subTy)
  substituteMany (TmVar v) ty typesStay namesStay typesSub namesSub (VarHasType prf) substitutions = case splitSumID v of
                                                                                                          (Left (y ** prfEq)) => (TmVar y ** ty ** subRefl ** VarHasType (keepTypeMatches v y namesSub typesSub namesStay typesStay prf prfEq))
                                                                                                          (Right (y ** prfEq)) => let (val ** _ ** subTy ** isSubTy ** hasSubty) = valueOnly {ty} (rewrite substituteTypeSame v y typesStay namesStay typesSub namesSub prf prfEq in (index y substitutions))
                                                                                                                                      (val' ** hasSubty') = shift (typeNamesToContext typesStay namesStay) [] (val ** hasSubty) in
                                                                                                                                      (val' ** subTy ** isSubTy ** hasSubty')
  substituteMany (TmAbs nm tyIn body) (TyArr tyIn tyOut) typesStay namesStay typesSub namesSub (AbsHasType bodyHasType) substitutions = let (body' ** bodySubty ** bodyIsSubty ** bodyHasType') = substituteMany body tyOut (tyIn :: typesStay) (nm :: namesStay) typesSub namesSub bodyHasType substitutions in
                                                                                                                                            (TmAbs nm tyIn body' ** (TyArr tyIn bodySubty) ** SubArrow subRefl bodyIsSubty ** AbsHasType bodyHasType')
  substituteMany (TmApp x y) ty typesStay namesStay typesSub namesSub (AppHasType xHasType isSubTy yHasType {varTy} {varSubTy}) substitutions =
    let (x' ** subX ** isSubX ** xHasType') = substituteMany x (TyArr varTy ty) typesStay namesStay typesSub namesSub xHasType substitutions
        (y' ** subY ** isSubY ** yHasType') = substituteMany y varSubTy typesStay namesStay typesSub namesSub yHasType substitutions in
        appHelper subX isSubX subY isSubY x' y' xHasType' yHasType'
        where
          appHelper : (subX : Ty) -> (isSubX : Subtype subX (TyArr varTy ty)) -> (subY : Ty) -> (isSubY : Subtype subY varSubTy) ->
                      (x, y : Term n) -> (xHasType : HasType (typeNamesToContext typesStay namesStay) x subX) -> (yHasType : HasType (typeNamesToContext typesStay namesStay) y subY) ->
                      (tOut : Term n ** (subTy : Ty ** (isSubType : Subtype subTy ty ** HasType (typeNamesToContext typesStay namesStay) tOut subTy)))
          appHelper (TyArr supIn subOut) (SubArrow subIns subOuts) subY isSubY x y xHasType yHasType = (TmApp x y ** subOut ** subOuts ** AppHasType xHasType (subTrans isSubY (subTrans isSubTy subIns)) yHasType)
  substituteMany (TmRec rec) (TyRec tyRec) typesStay namesStay typesSub namesSub (RecHasType recHasTy) substitutions = let (rec' ** recSubTy ** recIsSubTy ** recHasType') = substituteManyRec rec tyRec typesStay namesStay typesSub namesSub recHasTy substitutions in
                                                                                                                           (TmRec rec' ** TyRec recSubTy ** SubRcd recIsSubTy ** RecHasType recHasType')
  substituteMany (TmProj rec _) _ typesStay namesStay typesSub namesSub (ProjHasType i names types recHasTy {ok}) substitutions =
    let (rec' ** subTy ** isSubty ** recHasType') = substituteMany rec _ typesStay namesStay typesSub namesSub recHasTy substitutions in
        projHelper subTy isSubty rec' recHasType'
        where
          projHelper' : {0 names : BindingKeys} -> {0 types : Vect (length names) Ty} -> {i : Nat} -> {0 ok : InBounds i names} ->
                        (subNames : BindingKeys) -> (subTypes : Vect (length subNames) Ty) -> (subRcd : RecSub (MkRecordMap subNames subTypes) (MkRecordMap names types)) ->
                        (rec : Term n) -> (recHasType : HasType (typeNamesToContext typesStay namesStay) rec (TyRec (MkRecordMap subNames subTypes))) ->
                        (tOut : Term n ** (subTy : Ty ** (isSubType : Subtype subTy (index (inBoundsToFinLength i {ok} {set=names}) types) ** HasType (typeNamesToContext typesStay namesStay) tOut subTy)))
          projHelper' subNames subTypes RecSubEmpty rec recHasType {names=EmptySet} {ok} = void $ uninhabited ok
          projHelper' subNames subTypes (RecSubAdd _ isSub {typeB} {i} {ok}) rec recHasType {i = 0} {ok=InFirst}= (TmProj rec (index i subNames) ** index (inBoundsToFinLength i) subTypes ** isSub ** ProjHasType i subNames subTypes recHasType)
          projHelper' subNames subTypes (RecSubAdd subRcd _) rec recHasType {i = (S i)} {ok=InLater ok} = projHelper' subNames subTypes subRcd rec recHasType

          projHelper : (subTy : Ty) -> (isSubty : Subtype subTy (TyRec (MkRecordMap names types))) ->
                       (rec : Term n) -> (recHasType : HasType (typeNamesToContext typesStay namesStay) rec subTy) ->
                       (tOut : Term n ** (subTy : Ty ** (isSubType : Subtype subTy (index (inBoundsToFinLength i {ok}) types) ** HasType (typeNamesToContext typesStay namesStay) tOut subTy)))
          projHelper (TyRec (MkRecordMap subNames subTypes)) (SubRcd subRcd) = projHelper' subNames subTypes subRcd {names} {types} {i} {ok}

indexBigStepResultsIsBigStepIndex : (i : Fin n) -> (tyRec : Vect n Ty) -> BigStepResult (index i tyRec) = index i (BigStepResults tyRec)
indexBigStepResultsIsBigStepIndex FZ (ty :: _) = Refl
indexBigStepResultsIsBigStepIndex (FS i) (_ :: tyRec) = indexBigStepResultsIsBigStepIndex i tyRec

mutual
  weakenRec : {subNames,names : BindingKeys} -> {subTypes : Vect (length subNames) Ty} -> {types : Vect (length names) Ty} ->
              (subRcd : RecSub (MkRecordMap subNames subTypes) (MkRecordMap names types)) -> (res : HVect (BigStepResults subTypes)) ->
              HVect (BigStepResults types)
  weakenRec RecSubEmpty _ = []
  weakenRec (RecSubAdd subRcd subty {i} {ok}) res = let head=weakenType subty (rewrite indexBigStepResultsIsBigStepIndex (inBoundsToFinLength i {ok}) subTypes in index (inBoundsToFinLength i {ok}) res)
                                                        tail=weakenRec subRcd res in
                                                        (head :: tail)

  weakenType : {subTy, ty : Ty} -> Subtype subTy ty -> BigStepResult subTy -> BigStepResult ty
  weakenType SubTop res = let (val ** isVal ** subSubTy ** _ ** hasType) = valueOnly res in
                              (val ** isVal ** subSubTy ** SubTop ** hasType)
  weakenType (SubArrow subIns subOuts) ((val ** isVal ** subSubTy ** isSubSub ** hasType), res) = ((val ** isVal ** subSubTy ** subTrans isSubSub (SubArrow subIns subOuts) ** hasType)
                                                                                                  ,(\arg => weakenType subOuts (res (weakenType subIns arg)))
                                                                                                  )
  weakenType (SubRcd subRcd) {subTy = TyRec (MkRecordMap subNames subTypes)} {ty = TyRec (MkRecordMap names types)} ((val ** isVal ** subSubTy ** isSubSub ** hasType), res) =
    ((val ** isVal ** subSubTy ** subTrans isSubSub (SubRcd subRcd) ** hasType)
    ,weakenRec subRcd res
    )

mutual
  bigStepEvalGenRec' : (n : Nat) -> (recNames : BindingKeys) -> (terms : Vect (length recNames) (Term n)) -> (recTypes : Vect (length recNames) Ty) ->
                       (types : Vect n Ty) -> (names : Vect n String) -> (hasType : RecordMapHasType (typeNamesToContext types names) (MkRecordMap recNames terms) (MkRecordMap recNames recTypes)) ->
                       (substitutions : HVect (BigStepResult <$> types)) -> HVect (BigStepResults recTypes)
  bigStepEvalGenRec' n EmptySet [] [] types names hasType substitutions = []
  bigStepEvalGenRec' n (AddElement name recNames nameIsNew) (term :: terms) (ty :: recTypes) types names (ConsBindHasType headHasType tailHasType) substitutions =
    let headResult = bigStepEvalGen n term ty types names headHasType substitutions
        tailResult = bigStepEvalGenRec' n recNames terms recTypes types names tailHasType substitutions in
        headResult :: tailResult

  bigStepEvalGenRec : (n : Nat) -> (rec : RecordMap (Term n)) -> (tyRec : RecordMap Ty) -> (types : Vect n Ty) -> (names : Vect n String) -> (hasType : RecordMapHasType (typeNamesToContext types names) rec tyRec) -> (substitutions : HVect (BigStepResult <$> types)) -> BigStepResult (TyRec tyRec)
  bigStepEvalGenRec n (MkRecordMap EmptySet []) (MkRecordMap EmptySet []) types names NilBindHasType substitutions = ((TmRec (MkRecordMap EmptySet []) ** RecIsValue [] ** TyRec (MkRecordMap EmptySet []) ** SubRcd RecSubEmpty ** RecHasType NilBindHasType), [])
  bigStepEvalGenRec n (MkRecordMap (AddElement name recNames nameIsNew) (term :: termsTail)) (MkRecordMap (AddElement name recNames nameIsNew) (ty :: typesTail)) types names (ConsBindHasType headHasType tailHasType) substitutions =
    let bigStepResults = bigStepEvalGenRec' n (AddElement name recNames nameIsNew) (term :: termsTail) (ty :: typesTail) types names (ConsBindHasType headHasType tailHasType) substitutions in
        (unCurryValuesToRecVal _ _ (bigStepResultsToValues (AddElement name recNames nameIsNew) _ bigStepResults), bigStepResults)
        where
          valuesToRecVal : (recNames : BindingKeys) -> (recTypes : Vect (length recNames) Ty) ->
                           (terms : Vect (length recNames) (Term 0)) -> (isValue : All IsValue terms) -> (subTypes : Vect (length recNames) Ty) -> (areSubTypes : HVect (zipWith Subtype subTypes recTypes)) -> (haveTypes : RecordMapHasType [] (MkRecordMap recNames terms) (MkRecordMap recNames subTypes)) ->
                           CoreValue (TyRec (MkRecordMap recNames recTypes))
          valuesToRecVal recNames recTypes terms isValue subTypes areSubTypes haveTypes = (TmRec (MkRecordMap recNames terms) ** RecIsValue isValue ** TyRec (MkRecordMap recNames subTypes) ** SubRcd (recSubDepth recNames subTypes recTypes areSubTypes) ** RecHasType haveTypes)

          unCurryValuesToRecVal : (recNames : BindingKeys) -> (recTypes : Vect (length recNames) Ty) ->
                                  (terms : Vect (length recNames) (Term 0) ** isValue : All IsValue terms ** subTypes : Vect (length recNames) Ty ** areSubTypes : HVect (zipWith Subtype subTypes recTypes) ** RecordMapHasType [] (MkRecordMap recNames terms) (MkRecordMap recNames subTypes)) ->
                                  CoreValue (TyRec (MkRecordMap recNames recTypes))
          unCurryValuesToRecVal recNames recTypes (terms ** isValue ** subTypes ** areSubTypes ** hasTypes) = valuesToRecVal recNames recTypes terms isValue subTypes areSubTypes hasTypes

          bigStepResultsToValues : (recNames : BindingKeys) -> (recTypes : Vect (length recNames) Ty) -> (bigStepResults : HVect (BigStepResults recTypes)) ->
                                   (terms : Vect (length recNames) (Term 0) ** isValue : All IsValue terms ** subTypes : Vect (length recNames) Ty ** areSubTypes : HVect (zipWith Subtype subTypes recTypes) ** RecordMapHasType [] (MkRecordMap recNames terms) (MkRecordMap recNames subTypes))
          bigStepResultsToValues EmptySet [] [] = ([] ** [] ** [] ** [] ** NilBindHasType)
          bigStepResultsToValues (AddElement name recNames nameIsNew) (ty :: recTypes) (result :: results) =
            let (head ** headIsValue ** headTy ** headTyIsSub ** headIsType) = valueOnly result
                (tail ** tailIsValue ** tailTypes ** tailTypesAreSub ** tailIsType) = bigStepResultsToValues recNames recTypes results in
                (head :: tail ** headIsValue :: tailIsValue ** headTy :: tailTypes ** headTyIsSub :: tailTypesAreSub ** ConsBindHasType headIsType tailIsType)

  bigStepEvalGen : (n : Nat) -> (t : Term n) -> (tyOut : Ty) -> (types : Vect n Ty) -> (names : Vect n String) -> (hasType : HasType (typeNamesToContext types names) t tyOut) -> (substitutions : HVect (BigStepResult <$> types)) -> BigStepResult tyOut
  bigStepEvalGen n (TmVar v) tyOut types names (VarHasType prf) substitutions = rewrite typeNamesHelp prf {v} {types} in rewrite mapIndexCommutitive types v BigStepResult in index v substitutions
  bigStepEvalGen n (TmAbs name tyIn body) (TyArr tyIn tyOut) types names (AbsHasType bodyHasType) substitutions = let (body' ** subOut ** subOutIsSub ** bodyHasType') = substituteMany body tyOut [tyIn] [name] types names bodyHasType substitutions in
                                                                                                                      ( (TmAbs name tyIn body' ** AbsIsValue ** TyArr tyIn subOut ** SubArrow subRefl subOutIsSub ** AbsHasType bodyHasType')
                                                                                                                      , (\arg => bigStepEvalGen (S n) body tyOut (tyIn :: types) (name :: names) bodyHasType (arg :: substitutions))
                                                                                                                      )
  bigStepEvalGen n (TmApp x y) tyOut types names (AppHasType xHasType varIsSub yHasType {varTy} {varSubTy}) substitutions = let (_, xf) = bigStepEvalGen n x (TyArr varTy tyOut) types names xHasType substitutions
                                                                                                                                y'= bigStepEvalGen n y varSubTy types names yHasType substitutions in
                                                                                                                                xf (weakenType varIsSub y')
  bigStepEvalGen n (TmRec rec) (TyRec tyRec) types names (RecHasType recHasType) substitutions = bigStepEvalGenRec n rec tyRec types names recHasType substitutions
  bigStepEvalGen n (TmProj rec _) _ types names (ProjHasType i recNames tyRec recHasType {ok}) substitutions = let (_, recResult) = bigStepEvalGen n rec (TyRec (MkRecordMap recNames tyRec)) types names recHasType substitutions in
                                                                                                                   rewrite indexBigStepResultsIsBigStepIndex (inBoundsToFinLength i {ok}) tyRec in index (inBoundsToFinLength i) recResult

bigStepEval : (t : Term 0) -> (ty : Ty) -> (hasType : HasType [] t ty) -> BigStepResult ty
bigStepEval t ty hasType = bigStepEvalGen 0 t ty [] [] hasType []

export
bigStepEvalTerm : (t : Term 0) -> {ty : Ty} -> (hasType : HasType [] t ty) -> Term 0
bigStepEvalTerm t hasType = fst $ valueOnly $ bigStepEval t ty hasType
{--}
