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
import Data.Fun.Graph

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
    SubBot : Subtype TyBot b
    SubArrow : Subtype inB inA -> Subtype outA outB -> Subtype (TyArr inA outA) (TyArr inB outB)
    SubRcd : RecSub recA recB -> Subtype (TyRec recA) (TyRec recB)
    SubBool : Subtype TyBool TyBool

Uninhabited (Subtype (TyArr a b) (TyRec rec)) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible
  uninhabited SubBot impossible

Uninhabited (Subtype (TyRec rec) (TyArr a b)) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible
  uninhabited SubBot impossible

Uninhabited (Subtype TyTop (TyArr a b)) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible
  uninhabited SubBot impossible

Uninhabited (Subtype TyTop (TyRec rec)) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible
  uninhabited SubBot impossible

Uninhabited (Subtype TyTop TyBot) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible
  uninhabited SubBot impossible

Uninhabited (Subtype (TyRec rec) TyBot) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible
  uninhabited SubBot impossible

Uninhabited (Subtype (TyArr a b) TyBot) where
  uninhabited SubTop impossible
  uninhabited (SubArrow x y) impossible
  uninhabited (SubRcd x) impossible
  uninhabited SubBot impossible

recSubAddLeft : RecSub (MkRecordMap namesA typesA) b -> RecSub (MkRecordMap (AddElement nameA namesA nameANotInNamesA) (tyA :: typesA)) b
recSubAddLeft RecSubEmpty = RecSubEmpty
recSubAddLeft (RecSubAdd aRecSubB tyASubTyB {ok} {i} {typeB}) = rewrite succIndexOfAddElementEq i {ok} in RecSubAdd (recSubAddLeft aRecSubB) (replace (succIndexOfConsEq i) {p=(\x => Subtype x typeB)} tyASubTyB) {ok=succInbounds ok}

recSubAddBoth : {typeA, typeB : Ty} -> RecSub (MkRecordMap namesA typesA) (MkRecordMap namesB typesB) -> Subtype typeA typeB -> RecSub (MkRecordMap (AddElement name namesA nameNotInNamesA) (typeA :: typesA)) (MkRecordMap (AddElement name namesB nameNotInNamesB) (typeB :: typesB))
recSubAddBoth recSub subtype = RecSubAdd (recSubAddLeft recSub) subtype {i=0} {ok=InFirst}

recSubDepth :  (names : BindingKeys) -> (typesA, typesB : Vect (length names) Ty) -> (allTypesSub : HVect (zipWith Subtype typesA typesB)) -> RecSub (MkRecordMap names typesA) (MkRecordMap names typesB)
recSubDepth EmptySet [] [] [] = RecSubEmpty
recSubDepth (AddElement name names nameIsNew) (typeA :: typesA) (typeB :: typesB) (sub :: subs) =
  let tailSub = recSubDepth names typesA typesB subs in
      recSubAddBoth tailSub sub

missingMasterIsMissingRecSub : {name : String} -> {namesA, namesB : BindingKeys} -> {typesA : Vect (length namesA) Ty} -> {typesB : Vect (length namesB) Ty} -> (nameIsNew : SetMissing name namesA) -> (sub : RecSub (MkRecordMap namesA typesA) (MkRecordMap namesB typesB)) -> SetMissing name namesB
missingMasterIsMissingRecSub nameIsNew RecSubEmpty = EmptyMissing
missingMasterIsMissingRecSub nameIsNew (RecSubAdd sub _ {i}) = ConsMissing name (index i namesA) (setMissingToIndexNeq nameIsNew i) (missingMasterIsMissingRecSub nameIsNew sub)

mutual
  recSubRefl : {x : RecordMap Ty} -> RecSub x x
  recSubRefl {x = (MkRecordMap keys values)} = recSubRefl' keys values
    where
      recSubRefl' : (names : BindingKeys) -> (types : Vect (length names) Ty) -> RecSub (MkRecordMap names types) (MkRecordMap names types)
      recSubRefl' EmptySet [] = RecSubEmpty
      recSubRefl' (AddElement name names nameIsNew) (ty :: types) = recSubAddBoth (recSubRefl' names types) subRefl

  subRefl : {x : Ty} -> Subtype x x
  subRefl {x = (TyRec x)} = SubRcd recSubRefl
  subRefl {x = (TyArr x y)} = SubArrow subRefl subRefl
  subRefl {x = TyTop} = SubTop
  subRefl {x = TyBot} = SubBot
  subRefl {x = TyBool} = SubBool

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
  subTrans SubBot _ = SubBot
  subTrans (SubArrow insX outsX) (SubArrow insY outsY) = SubArrow (subTrans insY insX) (subTrans outsX outsY)
  subTrans (SubRcd x) (SubRcd y) = SubRcd (subRecTrans x y)
  subTrans SubBool SubBool = SubBool

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

  maybeSubType : (x, y : Ty) -> Maybe (Subtype x y)
  maybeSubType _ TyTop = Just SubTop
  maybeSubType TyBot _ = Just SubBot
  maybeSubType TyBool TyBool = Just SubBool
  maybeSubType (TyRec x) (TyRec y) with (decRecSub x y)
    maybeSubType (TyRec x) (TyRec y) | (Yes prf) = Just (SubRcd prf)
    maybeSubType (TyRec x) (TyRec y) | (No _) = Nothing
  maybeSubType (TyArr x z) (TyArr y w) with (maybeSubType y x)
    maybeSubType (TyArr x z) (TyArr y w) | Nothing = Nothing
    maybeSubType (TyArr x z) (TyArr y w) | (Just insSub) with (maybeSubType z w)
      maybeSubType (TyArr x z) (TyArr y w) | (Just insSub) | Nothing = Nothing
      maybeSubType (TyArr x z) (TyArr y w) | (Just insSub) | (Just outsSub) = Just (SubArrow insSub outsSub)
  maybeSubType _ _ = Nothing

  subtypeNotNothing : {x, y : Ty} -> Subtype x y -> Not (maybeSubType x y = Nothing)
  subtypeNotNothing SubTop prf = uninhabited prf
  subtypeNotNothing SubBot prf {y = (TyRec y)} = uninhabited prf
  subtypeNotNothing SubBot prf {y = (TyArr y z)} = uninhabited prf
  subtypeNotNothing SubBot prf {y = TyTop} = uninhabited prf
  subtypeNotNothing SubBot prf {y = TyBot} = uninhabited prf
  subtypeNotNothing SubBot prf {y = TyBool} = uninhabited prf
  subtypeNotNothing SubBool prf = uninhabited prf
  subtypeNotNothing (SubArrow a b) prf {x=TyArr x z} {y=TyArr y w} with (remember (maybeSubType y) x)
    subtypeNotNothing (SubArrow a b) prf {x=TyArr x z} {y=TyArr y w} | graph with (maybeSubType y x)
      subtypeNotNothing (SubArrow a b) prf {x=TyArr x z} {y=TyArr y w} | graph | Nothing = subtypeNotNothing a (graph.proof)
      subtypeNotNothing (SubArrow a b) prf {x=TyArr x z} {y=TyArr y w} | graph | Just insSub with (remember (maybeSubType z) w)
        subtypeNotNothing (SubArrow a b) prf {x=TyArr x z} {y=TyArr y w} | graph | Just insSub | graph2 with (maybeSubType z w)
          subtypeNotNothing (SubArrow a b) prf {x=TyArr x z} {y=TyArr y w} | graph | Just insSub | graph2 | Nothing = subtypeNotNothing b (graph2.proof)
          subtypeNotNothing (SubArrow a b) prf {x=TyArr x z} {y=TyArr y w} | graph | Just insSub | graph2 | Just outsSub = uninhabited prf
  subtypeNotNothing (SubRcd z) prf {x = (TyRec recA)} {y = (TyRec recB)} with (decRecSub recA recB)
    subtypeNotNothing (SubRcd z) prf {x = (TyRec recA)} {y = (TyRec recB)} | (No contra) = contra z
    subtypeNotNothing (SubRcd z) prf {x = (TyRec recA)} {y = (TyRec recB)} | (Yes prf2) = uninhabited prf

  decSubtype : (x, y : Ty) -> Dec (Subtype x y)
  decSubtype x y with (remember (maybeSubType x) y)
    decSubtype x y | graph with (maybeSubType x y)
      decSubtype x y | graph | (Just subty) = Yes subty
      decSubtype x y | graph | Nothing = No (\subty => subtypeNotNothing subty graph.proof)

mutual
  data RecordMapHasType : {n : Nat} -> Context n  -> RecordMap (Term n) -> RecordMap Ty -> Type where
    NilBindHasType : RecordMapHasType context (MkRecordMap EmptySet []) (MkRecordMap EmptySet [])
    ConsBindHasType : (headHasType : HasType context term ty) -> (tailHasType : RecordMapHasType context (MkRecordMap keysTail termsTail) (MkRecordMap keysTail typesTail)) -> RecordMapHasType context (MkRecordMap (AddElement name keysTail nameIsNew) (term :: termsTail)) (MkRecordMap (AddElement name keysTail nameIsNew) (ty :: typesTail))

  data HasType : {n : Nat} -> Context n -> Term n -> Ty -> Type where
    VarHasType : getBindingType context v = type -> HasType context (TmVar v) type
    AbsHasType : (bodyHasType : HasType (addBinding context name varTy) body type) -> HasType context (TmAbs name varTy body) (TyArr varTy type)
    AppHasType : {varTy,varSubTy : Ty} -> (xHasType : HasType context x (TyArr varTy returnTy)) -> (isSub : Subtype varSubTy varTy) -> (yHasType : HasType context y varSubTy) -> HasType context (TmApp x y) returnTy
    AppBotHasType : {varTy : Ty} -> (xIsBot : HasType context x TyBot) -> (yHasType : HasType context y varTy) -> HasType context (TmApp x y) TyBot
    RecHasType : RecordMapHasType context recBinds tyBinds -> HasType context (TmRec recBinds) (TyRec tyBinds)
    ProjHasType : (i : Nat) -> (names : BindingKeys) -> (types : Vect (length names) Ty) -> HasType context rec (TyRec (MkRecordMap names types)) -> {auto 0 ok : InBounds i names} -> HasType context (TmProj rec (index i names)) (index (inBoundsToFinLength i {ok}) types)
    ProjBotHasType : (recIsBot : HasType context rec TyBot) -> HasType context (TmProj rec name) TyBot
    TrueHasType : HasType context TmTrue TyBool
    FalseHasType : HasType context TmFalse TyBool
    IfHasType : {thenTy, elseTy : Ty} -> HasType context guardTerm TyBool -> HasType context thenTerm thenTy -> HasType context elseTerm elseTy -> Subtype thenTy resTy -> Subtype elseTy resTy -> HasType context (TmIf guardTerm thenTerm elseTerm) resTy
    IfBotHasType : {thenTy, elseTy : Ty} -> HasType context guardTerm TyBot -> HasType context thenTerm thenTy -> HasType context elseTerm elseTy -> HasType context (TmIf guardTerm thenTerm elseTerm) TyBot

swapStartIsSub : (nameA, nameB : String) -> (names : BindingKeys) -> (typeA, typeB : Ty) -> (types : Vect (length names) Ty) ->
                 {nameBNotNames : SetMissing nameB names} -> {nameANotNameBNames : SetMissing nameA (AddElement nameB names nameBNotNames)} ->
                 {nameANotNames : SetMissing nameA names} -> {nameBNotNameANames : SetMissing nameB (AddElement nameA names nameANotNames)} ->
                 RecSub (MkRecordMap (AddElement nameA (AddElement nameB names nameBNotNames) nameANotNameBNames) (typeA :: typeB :: types)) (MkRecordMap (AddElement nameB (AddElement nameA names nameANotNames) nameBNotNameANames) (typeB :: typeA :: types))
swapStartIsSub nameA nameB names typeA typeB types = RecSubAdd (RecSubAdd (recSubAddLeft $ recSubAddLeft (recSubRefl)) subRefl {i=0} {ok=InFirst}) subRefl {i=1} {ok=InLater InFirst}

pullIndexToFront : (names : BindingKeys) -> (types : Vect (length names) Ty) -> (i : Nat) -> {0 ok : InBounds i names} ->
                   (permNames : BindingKeys ** permTypes : Vect (length permNames) Ty ** isMissing : SetMissing (index i names) permNames
                   ** isSub : RecSub (MkRecordMap (AddElement (index i names) permNames isMissing) (index (inBoundsToFinLength i {ok}) types :: permTypes)) (MkRecordMap names types)
                   ** RecSub (MkRecordMap names types) (MkRecordMap permNames permTypes)
                   )
pullIndexToFront (AddElement name names nameIsNew) (type :: types) 0 {ok=InFirst} = (names ** types ** nameIsNew ** recSubRefl ** recSubAddLeft recSubRefl)
pullIndexToFront (AddElement name names nameIsNew) (type :: types) (S i) {ok=InLater ok} =
  let (names' ** types' ** isMissing ** isSub ** isSup) = pullIndexToFront names types i in
      (AddElement name names' (missingMasterIsMissingRecSub nameIsNew isSup) ** type :: types'
      ** ConsMissing (index i names) name (symNeq $ setMissingToIndexNeq nameIsNew i) isMissing
      ** subRecTrans (swapStartIsSub (index i names) name names' (index (inBoundsToFinLength i) types) type types' {nameBNotNameANames = (missingMasterIsMissingRecSub nameIsNew (RecSubAdd isSup subRefl))}) (recSubAddBoth isSub subRefl)
      ** recSubAddBoth isSup subRefl)

unwrapRecSubAdd : {namesA : BindingKeys} -> {typesA : Vect (length namesA) Ty} ->  {nameMissing : SetMissing name otherNames} ->
                  RecSub (MkRecordMap namesA typesA) (MkRecordMap (AddElement name namesB nameIsNew) (type :: typesB)) ->
                  (recSub : RecSub (MkRecordMap namesA typesA) (MkRecordMap namesB typesB) ** i : Nat ** Exists {type = (InBounds i namesA)} (\ok => (subTy : Subtype (index (inBoundsToFinLength i {ok}) typesA) type ** isIndex : name = index i namesA ** indexMissingOtherNames : SetMissing (index i namesA) otherNames ** AddElement name otherNames nameMissing = AddElement (index i namesA) otherNames indexMissingOtherNames)))
unwrapRecSubAdd (RecSubAdd recSub subty {i} {ok}) = (recSub ** i ** Evidence ok (subty ** Refl ** nameMissing ** Refl))

mutual
  recJoin' : (namesA, namesB : BindingKeys) -> (typesA : Vect (length namesA) Ty) -> (typesB : Vect (length namesB) Ty) -> (jRecTy : RecordMap Ty ** aSub : RecSub (MkRecordMap namesA typesA) jRecTy ** RecSub (MkRecordMap namesB typesB) jRecTy)
  recJoin' EmptySet namesB [] typesB = (MkRecordMap EmptySet [] ** RecSubEmpty ** RecSubEmpty)
  recJoin' (AddElement nameA namesA nameAIsNew) namesB (typeA :: typesA) typesB with (getIndex nameA namesB)
    recJoin' (AddElement nameA namesA nameAIsNew) namesB (typeA :: typesA) typesB | (Left _) = let (joinRec ** subA ** subB)=recJoin' namesA namesB typesA typesB in
                                                                                                   (joinRec ** recSubAddLeft subA ** subB)
    recJoin' (AddElement nameA namesA nameAIsNew) namesB (typeA :: typesA) typesB | (Right (i ** inBounds ** isIndex)) =
      let (MkRecordMap joinNames joinTypes ** subA ** subB)=recJoin' namesA namesB typesA typesB
          (joinTy ** subtyA ** subtyB) = Eval.join typeA (index (inBoundsToFinLength i) typesB) in
          (  MkRecordMap (AddElement nameA joinNames (missingMasterIsMissingRecSub nameAIsNew subA)) (joinTy :: joinTypes)
          ** rewrite sym $ index0OfAddElementNew {set=namesA} {isNew=nameAIsNew} in recSubAddBoth subA subtyA
          ** rewrite isIndex in RecSubAdd subB subtyB
          )

  recJoin : (a, b : RecordMap Ty) -> (jRecTy : RecordMap Ty ** aSub : RecSub a jRecTy ** RecSub b jRecTy)
  recJoin (MkRecordMap namesA typesA) (MkRecordMap namesB typesB) = recJoin' namesA namesB typesA typesB

  join : (a, b : Ty) -> (jTy : Ty ** aSub : Subtype a jTy ** Subtype b jTy)
  join (TyRec a) (TyRec b) = let (recTy ** recSubA ** recSubB) = recJoin a b in
                                 (TyRec recTy ** SubRcd recSubA ** SubRcd recSubB)
  join (TyArr x y) (TyArr z w) = let (insMeet ** insSubA ** insSubB) = meet x z
                                     (outsJoin ** outsSubA ** outsSubB) = join y w in
                                     (TyArr insMeet outsJoin ** SubArrow insSubA outsSubA ** SubArrow insSubB outsSubB)
  join TyBot b = (b ** SubBot ** subRefl)
  join TyBool TyBool = (TyBool ** SubBool ** SubBool)
  join _ _ = (TyTop ** SubTop ** SubTop)

  recMeet' : (namesA, namesB : BindingKeys) -> (typesA : Vect (length namesA) Ty) -> (typesB : Vect (length namesB) Ty) -> (mRecTy : RecordMap Ty ** aSub : RecSub mRecTy (MkRecordMap namesA typesA) ** RecSub mRecTy (MkRecordMap namesB typesB))
  recMeet' EmptySet namesB [] typesB = (MkRecordMap namesB typesB ** RecSubEmpty ** recSubRefl)
  recMeet' (AddElement nameA namesA nameAIsNew) namesB (typeA :: typesA) typesB with (getIndex nameA namesB)
    recMeet' (AddElement nameA namesA nameAIsNew) namesB (typeA :: typesA) typesB | (Left nameANotInNamesB) =
      let (MkRecordMap namesMeet typesMeet ** subA ** RecSubAdd subB subty)=recMeet' namesA (AddElement nameA namesB nameANotInNamesB) typesA (typeA :: typesB) in
          (MkRecordMap namesMeet typesMeet ** RecSubAdd subA subty ** subB)
    recMeet' (AddElement nameA namesA nameAIsNew) namesB (typeA :: typesA) typesB | (Right (i ** inBounds ** isIndex)) =
      let (meetType ** subtyA ** subtyB) = meet typeA (index (inBoundsToFinLength i) typesB)
          (restNames ** restType ** indIsMissing ** isSub ** isSup) = pullIndexToFront namesB typesB i
          (MkRecordMap namesMeet typesMeet ** subA ** subB) = recMeet' namesA (AddElement (index i namesB) restNames indIsMissing) typesA (meetType :: restType)
          (subB' ** j ** Evidence jInBounds (indJSubty ** isJIndex ** indIsMissing' ** addElementRestSame)) = unwrapRecSubAdd subB {otherNames = restNames} {nameMissing = indIsMissing} in
          (MkRecordMap namesMeet typesMeet ** rewrite (trans isIndex isJIndex) in RecSubAdd subA (subTrans indJSubty subtyA) ** subRecTrans (rewrite addElementRestSame in RecSubAdd subB' (subTrans indJSubty subtyB)) isSub)

  recMeet : (a, b : RecordMap Ty) -> (mRecTy : RecordMap Ty ** aSub : RecSub mRecTy a ** RecSub mRecTy b)
  recMeet (MkRecordMap namesA typesA) (MkRecordMap namesB typesB) = recMeet' namesA namesB typesA typesB

  meet : (a, b : Ty) -> (mTy : Ty ** aSub : Subtype mTy a ** Subtype mTy b)
  meet (TyRec a) (TyRec b) = let (recTy ** recSubA ** recSubB) = recMeet a b in
                                 (TyRec recTy ** SubRcd recSubA ** SubRcd recSubB)
  meet (TyArr x y) (TyArr z w) = let (insJoin ** insSubA ** insSubB) = join x z
                                     (outsMeet ** outsSubA ** outsSubB) = meet y w in
                                     (TyArr insJoin outsMeet ** SubArrow insSubA outsSubA ** SubArrow insSubB outsSubB)
  meet TyTop b = (b ** SubTop ** subRefl)
  meet TyBool TyBool = (TyBool ** SubBool ** SubBool)
  meet _ _ = (TyBot ** SubBot ** SubBot)

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
  getType context (TmApp x y) = do (subTy ** subHasType) <- getType context y
                                   ((TyArr var return) ** funcHasType) <- getType context x
                                      | (TyBot ** funcIsBot) => Right (TyBot ** (AppBotHasType funcIsBot subHasType))
                                      | _ => Left "Expected function type in application"
                                   case decSubtype subTy var of
                                        (Yes subType) => Right (return ** (AppHasType funcHasType subType subHasType))
                                        (No _) => Left "Type passed to application is not a subtype of argument to function"
  getType context (TmRec (MkRecordMap names terms)) = do (tyRec ** recHasType) <- getRecTypes context names terms
                                                         Right (TyRec tyRec ** RecHasType recHasType)
  getType context (TmProj rec name) = do (TyRec (MkRecordMap names types) ** recHasType) <- getType context rec
                                          | (TyBot ** recIsBot) => Right (TyBot ** (ProjBotHasType recIsBot))
                                          | _ => Left "Expected record type in projection"
                                         case getIndex name names of
                                              Left _ => Left (name ++ " is not a label in record")
                                              (Right (n ** inBounds ** isIndex)) => Right (index (inBoundsToFinLength n) types ** rewrite isIndex in ProjHasType n names types recHasType)
  getType context TmTrue = Right (TyBool ** TrueHasType)
  getType context TmFalse = Right (TyBool ** FalseHasType)
  getType context (TmIf g t e) = do (guardType ** guardHasType) <- getType context g
                                    (thenType ** thenHasType) <- getType context t
                                    (elseType ** elseHasType) <- getType context e
                                    case guardType of
                                         TyBot => Right (TyBot ** IfBotHasType guardHasType thenHasType elseHasType)
                                         TyBool => let (joinTy ** subThen ** subElse) = join thenType elseType in
                                                       Right (joinTy ** IfHasType guardHasType thenHasType elseHasType subThen subElse)
                                         _ => Left "Expected bool type in guard"

data IsValue : Term n -> Type where
  AbsIsValue : IsValue (TmAbs name ty body)
  RecIsValue : {0 names : BindingKeys} -> {0 recTerms : Vect (length names) (Term n)} -> All IsValue recTerms -> IsValue (TmRec (MkRecordMap names recTerms))
  TrueIsValue : IsValue TmTrue
  FalseIsValue : IsValue TmFalse

CoreValue : (ty : Ty) -> Type
CoreValue ty = (t : Term 0 ** isValue : IsValue t ** subTy : Ty ** isSubtype : Subtype subTy ty ** HasType [] t subTy)

mutual
  BigStepResults : (Vect n Ty) -> Vect n Type
  BigStepResults [] = []
  BigStepResults (ty :: tys) = BigStepResult ty :: BigStepResults tys

  BigStepResult : (ty : Ty) -> Type
  BigStepResult TyTop = CoreValue TyTop
  BigStepResult TyBool = (CoreValue TyBool, Bool)
  BigStepResult (TyRec (MkRecordMap names types)) = (CoreValue (TyRec (MkRecordMap names types)), HVect (BigStepResults types))
  BigStepResult (TyArr tyIn tyOut) = (CoreValue (TyArr tyIn tyOut), (BigStepResult tyIn) -> (BigStepResult tyOut))
  BigStepResult TyBot = Void

valueOnly : {ty : Ty} -> BigStepResult ty -> CoreValue ty
valueOnly {ty = TyTop} x = x
valueOnly {ty = TyBool} (x, _) = x
valueOnly {ty = TyRec (MkRecordMap _ _)} (x, _) = x
valueOnly {ty = TyArr _ _} (x, _) = x
valueOnly {ty = TyBot} x = void x

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
  shift extra context ((TmApp x y) ** (AppBotHasType xIsBot yHasType)) = let (x' ** xIsBot') = shift extra context (x ** xIsBot)
                                                                             (y' ** yHasType') = shift extra context (y ** yHasType) in
                                                                             (TmApp x' y' ** AppBotHasType xIsBot' yHasType')
  shift extra context ((TmApp x y) ** (AppHasType xHasType argIsSubType yHasType)) = let (x' ** xHasType') = shift extra context (x ** xHasType)
                                                                                         (y' ** yHasType') = shift extra context (y ** yHasType) in
                                                                                         (TmApp x' y' ** AppHasType xHasType' argIsSubType yHasType')
  shift extra context ((TmRec (MkRecordMap names terms)) ** (RecHasType recHasType)) = let (rec' ** recHasType') = shiftRec extra context names terms recHasType in
                                                                                           (TmRec rec' ** RecHasType recHasType')
  shift extra context ((TmProj rec name) ** (ProjBotHasType recIsBot)) = let (rec' ** recIsBot') = shift extra context (rec ** recIsBot) in
                                                                             (TmProj rec' name ** ProjBotHasType recIsBot')
  shift extra context ((TmProj rec _) ** (ProjHasType i names types recHasType)) = let (rec' ** recHasType') = shift extra context (rec ** recHasType) in
                                                                                       (TmProj rec' (index i names) ** (ProjHasType i names types recHasType'))
  shift extra context (TmTrue ** TrueHasType) = (TmTrue ** TrueHasType)
  shift extra context (TmFalse ** FalseHasType) = (TmFalse ** FalseHasType)
  shift extra context ((TmIf g t e) ** (IfBotHasType gIsBot tHasType eHasType)) = let (g' ** gIsBot') = shift extra context (g ** gIsBot)
                                                                                      (t' ** tHasType') = shift extra context (t ** tHasType)
                                                                                      (e' ** eHasType') = shift extra context (e ** eHasType) in
                                                                                      (TmIf g' t' e' ** IfBotHasType gIsBot' tHasType' eHasType')
  shift extra context ((TmIf g t e) ** (IfHasType gHasType tHasType eHasType subT subE)) = let (g' ** gHasType') = shift extra context (g ** gHasType)
                                                                                               (t' ** tHasType') = shift extra context (t ** tHasType)
                                                                                               (e' ** eHasType') = shift extra context (e ** eHasType) in
                                                                                               (TmIf g' t' e' ** IfHasType gHasType' tHasType' eHasType' subT subE)


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
            (term' :: terms' ** subty :: subtypes ** recSubAddBoth areSubTypes isSubty ** ConsBindHasType hasSubty haveSubtypes)

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
  substituteMany (TmApp x y) TyBot typesStay namesStay typesSub namesSub (AppBotHasType xIsBot yHasType {varTy}) substitutions =
    let (x' ** subX ** isSubX ** xHasType') = substituteMany x TyBot typesStay namesStay typesSub namesSub xIsBot substitutions
        (y' ** subY ** isSubY ** yHasType') = substituteMany y varTy typesStay namesStay typesSub namesSub yHasType substitutions in
        appBotHelper subX isSubX x' y' xHasType' subY yHasType'
        where
          appBotHelper : (subX : Ty) -> (isSubX : Subtype subX TyBot) ->
                         (x, y : Term n) -> (xHasType : HasType (typeNamesToContext typesStay namesStay) x subX) -> (subY : Ty) -> (yHasType : HasType (typeNamesToContext typesStay namesStay) y subY) ->
                         (tOut : Term n ** (subTy : Ty ** (isSubType : Subtype subTy TyBot ** HasType (typeNamesToContext typesStay namesStay) tOut subTy)))
          appBotHelper TyBot SubBot x y xHasType subY yHasType = (TmApp x y ** TyBot ** SubBot ** AppBotHasType xHasType yHasType)
  substituteMany (TmApp x y) ty typesStay namesStay typesSub namesSub (AppHasType xHasType isSubTy yHasType {varTy} {varSubTy}) substitutions =
    let (x' ** subX ** isSubX ** xHasType') = substituteMany x (TyArr varTy ty) typesStay namesStay typesSub namesSub xHasType substitutions
        (y' ** subY ** isSubY ** yHasType') = substituteMany y varSubTy typesStay namesStay typesSub namesSub yHasType substitutions in
        appHelper subX isSubX subY isSubY x' y' xHasType' yHasType'
        where
          appHelper : (subX : Ty) -> (isSubX : Subtype subX (TyArr varTy ty)) -> (subY : Ty) -> (isSubY : Subtype subY varSubTy) ->
                      (x, y : Term n) -> (xHasType : HasType (typeNamesToContext typesStay namesStay) x subX) -> (yHasType : HasType (typeNamesToContext typesStay namesStay) y subY) ->
                      (tOut : Term n ** (subTy : Ty ** (isSubType : Subtype subTy ty ** HasType (typeNamesToContext typesStay namesStay) tOut subTy)))
          appHelper TyBot SubBot subY isSubY x y xHasType yHasType = (TmApp x y ** TyBot ** SubBot ** AppBotHasType xHasType yHasType)
          appHelper (TyArr supIn subOut) (SubArrow subIns subOuts) subY isSubY x y xHasType yHasType = (TmApp x y ** subOut ** subOuts ** AppHasType xHasType (subTrans isSubY (subTrans isSubTy subIns)) yHasType)
  substituteMany (TmRec rec) (TyRec tyRec) typesStay namesStay typesSub namesSub (RecHasType recHasTy) substitutions = let (rec' ** recSubTy ** recIsSubTy ** recHasType') = substituteManyRec rec tyRec typesStay namesStay typesSub namesSub recHasTy substitutions in
                                                                                                                           (TmRec rec' ** TyRec recSubTy ** SubRcd recIsSubTy ** RecHasType recHasType')
  substituteMany (TmProj rec name) TyBot typesStay namesStay typesSub namesSub (ProjBotHasType recIsBot) substitutions =
    let (rec' ** subTy ** isSubty ** recIsBot') = substituteMany rec _ typesStay namesStay typesSub namesSub recIsBot substitutions in
        projBotHelper subTy isSubty rec' recIsBot'
        where
          projBotHelper : (subTy : Ty) -> (isSubty : Subtype subTy TyBot) ->
                          (rec : Term n) -> (recIsBot : HasType (typeNamesToContext typesStay namesStay) rec subTy) ->
                          (tOut : Term n ** (subTy : Ty ** (isSubType : Subtype subTy TyBot ** HasType (typeNamesToContext typesStay namesStay) tOut subTy)))
          projBotHelper TyBot SubBot rec recIsBot = (TmProj rec name ** TyBot ** SubBot ** ProjBotHasType recIsBot)
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
          projHelper (TyRec (MkRecordMap subNames subTypes)) (SubRcd subRcd) rec recHasType = projHelper' subNames subTypes subRcd {names} {types} {i} {ok} rec recHasType
          projHelper TyBot SubBot rec recHasType = (TmProj rec (index i names) ** TyBot ** SubBot ** ProjBotHasType recHasType)
  substituteMany TmTrue TyBool typesStay namesStay typesSub namesSub TrueHasType substitutions = (TmTrue ** TyBool ** SubBool ** TrueHasType)
  substituteMany TmFalse TyBool typesStay namesStay typesSub namesSub FalseHasType substitutions = (TmFalse ** TyBool ** SubBool ** FalseHasType)
  substituteMany (TmIf g t e) TyBot typesStay namesStay typesSub namesSub (IfBotHasType gIsBot tHasType eHasType {thenTy} {elseTy}) substitutions =
    let (g' ** subG ** isSubG ** gIsBot') = substituteMany g TyBot typesStay namesStay typesSub namesSub gIsBot substitutions
        (t' ** _ ** _ ** tHasType') = substituteMany t thenTy typesStay namesStay typesSub namesSub tHasType substitutions
        (e' ** _ ** _ ** eHasType') = substituteMany e elseTy typesStay namesStay typesSub namesSub eHasType substitutions in
        ifBotHelper subG isSubG g' t' e' gIsBot' tHasType' eHasType'
        where
          ifBotHelper : (subG : Ty) -> (isSubG : Subtype subG TyBot) ->
                        {thenTy, elseTy : Ty} ->
                        (g, t, e : Term n) -> (gIsBot : HasType (typeNamesToContext typesStay namesStay) g subG) -> (tHasType : HasType (typeNamesToContext typesStay namesStay) t thenTy) -> (eHasType : HasType (typeNamesToContext typesStay namesStay) e elseTy) ->
                        (tOut : Term n ** (subTy : Ty ** (isSubType : Subtype subTy TyBot ** HasType (typeNamesToContext typesStay namesStay) tOut subTy)))
          ifBotHelper TyBot SubBot g t e gIsBot tHasType eHasType = (TmIf g t e ** TyBot ** SubBot ** IfBotHasType gIsBot tHasType eHasType)
  substituteMany (TmIf g t e) ty typesStay namesStay typesSub namesSub (IfHasType gHasType tHasType eHasType isSubT isSubE {thenTy} {elseTy}) substitutions =
    let (g' ** subG ** isSubG ** gHasType') = substituteMany g TyBool typesStay namesStay typesSub namesSub gHasType substitutions
        (t' ** subT ** isSubT' ** tHasType') = substituteMany t thenTy typesStay namesStay typesSub namesSub tHasType substitutions
        (e' ** subE ** isSubE' ** eHasType') = substituteMany e elseTy typesStay namesStay typesSub namesSub eHasType substitutions in
        ifHelper subG isSubG g' t' e' gHasType' tHasType' eHasType' (subTrans isSubT' isSubT) (subTrans isSubE' isSubE)
        where
          ifHelper : (subG : Ty) -> (isSubG : Subtype subG TyBool) ->
                     {thenTy, elseTy : Ty} ->
                     (g, t, e : Term n) -> (gHasType : HasType (typeNamesToContext typesStay namesStay) g subG) -> (tHasType : HasType (typeNamesToContext typesStay namesStay) t thenTy) -> (eHasType : HasType (typeNamesToContext typesStay namesStay) e elseTy) ->
                     (subT : Subtype thenTy ty) -> (subE : Subtype elseTy ty) ->
                     (tOut : Term n ** (subTy : Ty ** (isSubType : Subtype subTy ty ** HasType (typeNamesToContext typesStay namesStay) tOut subTy)))
          ifHelper TyBool SubBool g t e gHasType tHasType eHasType subT subE = (TmIf g t e ** ty ** subRefl ** IfHasType gHasType tHasType eHasType subT subE)
          ifHelper TyBot SubBot g t e gHasType tHasType eHasType subT subE = (TmIf g t e ** TyBot ** SubBot ** IfBotHasType gHasType tHasType eHasType)

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
  weakenType SubBot res = void res
  weakenType SubBool res = res

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
  bigStepEvalGen n (TmApp x y) TyBot types names (AppBotHasType xIsBot yHasType {varTy}) substitutions = void $ bigStepEvalGen n x TyBot types names xIsBot substitutions --Void is Void, pass to void to erase
  bigStepEvalGen n (TmApp x y) tyOut types names (AppHasType xHasType varIsSub yHasType {varTy} {varSubTy}) substitutions = let (_, xf) = bigStepEvalGen n x (TyArr varTy tyOut) types names xHasType substitutions
                                                                                                                                y'= bigStepEvalGen n y varSubTy types names yHasType substitutions in
                                                                                                                                xf (weakenType varIsSub y')
  bigStepEvalGen n (TmRec rec) (TyRec tyRec) types names (RecHasType recHasType) substitutions = bigStepEvalGenRec n rec tyRec types names recHasType substitutions
  bigStepEvalGen n (TmProj rec name) TyBot types names (ProjBotHasType recIsBot) substitutions = void $ bigStepEvalGen n rec TyBot types names recIsBot substitutions --Void is Void, pass to void to erase
  bigStepEvalGen n (TmProj rec _) _ types names (ProjHasType i recNames tyRec recHasType {ok}) substitutions = let (_, recResult) = bigStepEvalGen n rec (TyRec (MkRecordMap recNames tyRec)) types names recHasType substitutions in
                                                                                                                   rewrite indexBigStepResultsIsBigStepIndex (inBoundsToFinLength i {ok}) tyRec in index (inBoundsToFinLength i) recResult
  bigStepEvalGen n TmTrue TyBool types names TrueHasType substitutions = ((TmTrue ** TrueIsValue ** TyBool ** SubBool ** TrueHasType), True)
  bigStepEvalGen n TmFalse TyBool types names FalseHasType substitutions = ((TmFalse ** FalseIsValue ** TyBool ** SubBool ** FalseHasType), False)
  bigStepEvalGen n (TmIf g _ _) TyBot types names (IfBotHasType gIsBot _ _) substitutions = void $ bigStepEvalGen n g TyBot types names gIsBot substitutions
  bigStepEvalGen n (TmIf g t e) tyOut types names (IfHasType gHasType tHasType eHasType subT subE {thenTy} {elseTy}) substitutions =
    let (_,g') = bigStepEvalGen n g TyBool types names gHasType substitutions in
        if g'
           then let t' = bigStepEvalGen n t thenTy types names tHasType substitutions in
                    weakenType subT t'
           else let e' = bigStepEvalGen n e elseTy types names eHasType substitutions in
                    weakenType subE e'

bigStepEval : (t : Term 0) -> (ty : Ty) -> (hasType : HasType [] t ty) -> BigStepResult ty
bigStepEval t ty hasType = bigStepEvalGen 0 t ty [] [] hasType []

export
bigStepEvalTerm : (t : Term 0) -> {ty : Ty} -> (hasType : HasType [] t ty) -> Term 0
bigStepEvalTerm t hasType = fst $ valueOnly $ bigStepEval t ty hasType
{--}
