module TypeCheck

import Context
import Term
import Ty

import Decidable.Equality

%default total

public export
data HasType : {m, n : Nat} -> Context m n -> Term m n -> Ty n -> Type where
  VarHasType : TermHasTypeInContext ind ty context -> HasType context (TmVar ind) ty
  AbsHasType : {name : _ } -> HasType (addTermBinding context name ty) body bTy -> HasType context (TmAbs ty body) (TyArr ty bTy)
  AppHasType : {tArg : Ty n} -> HasType context func (TyArr tArg tRes) -> HasType context arg tArg -> HasType context (TmApp func arg) tRes
  TAbsHasType : {name : String} -> HasType (addTypeBinding context name) body bTy -> HasType context (TmTAbs body) (TyAll bTy)
  TAppHasType : {bTy : Ty (S n)} -> HasType context uni (TyAll bTy) -> HasType context (TmTApp uni arg) (substituteFirst arg bTy)
  PackHasType : HasType context some (substituteFirst ty someTy) -> HasType context (TmPack ty some (TySome someTy)) (TySome someTy)
  UnpackHasType : {tyName, tmName: String} -> {packType : Ty (S n)} -> {bodyType : Ty (S n)} -> HasType context package (TySome packType) -> HasType (addTermBinding (addTypeBinding context tyName) tmName packType) body bodyType -> (bodyCanShiftDown : CanShiftDown FZ bodyType) -> HasType context (TmUnpack package body) (shiftDown bodyType FZ bodyCanShiftDown)

hasType : {n : _} -> (context : Context m n) -> (term : Term m n) -> Either String (ty : Ty n ** HasType context term ty)
hasType context (TmVar ind) = let (ty ** varHasType) = getTermBindingType context ind
                               in Right (ty ** VarHasType varHasType)
hasType context (TmAbs ty body) = do (bTy ** bodyHasType) <- hasType (addTermBinding context "" ty) body
                                     Right (TyArr ty bTy ** AbsHasType bodyHasType)
hasType context (TmApp func arg) = do (TyArr argType resType ** funcHasType) <- hasType context func
                                      | _ => Left "Expected function type in application"
                                      (argType' ** argHasType) <- hasType context arg
                                      case decEq argType' argType of
                                           (Yes prf) => Right (resType ** AppHasType (rewrite prf in funcHasType) argHasType)
                                           (No contra) => Left "Argument type must match function type"
hasType context (TmTAbs body) = do (bTy ** bodyHasType) <- hasType (addTypeBinding context "") body
                                   Right (TyAll bTy ** TAbsHasType bodyHasType)
hasType context (TmTApp uni argTy) = do (TyAll uniType ** uniHasType) <- hasType context uni
                                        | _ => Left "Expected universal type in type applicaiton"
                                        Right (substituteFirst argTy uniType ** TAppHasType uniHasType)
hasType context (TmPack aTy body (TySome someTy)) = do (bTy ** bodyHasType) <- hasType context body
                                                       case decEq (substituteFirst aTy someTy) bTy of
                                                            (Yes prf) => Right (TySome someTy ** PackHasType (rewrite prf in bodyHasType))
                                                            (No contra) => Left "Package type doesn't match package value"
hasType context (TmPack aTy body _) = Left "Expected existional type in package definition"
hasType context (TmUnpack pack body) = do (TySome packTy ** packHasType) <- hasType context pack
                                          | _ => Left "Expected extensional type in unpack"
                                          (bodyTy ** bodyHasType) <- hasType (addTermBinding (addTypeBinding context "") "" packTy) body
                                          case canShiftDown FZ bodyTy of
                                               (Yes canShift) => Right (shiftDown bodyTy FZ canShift ** UnpackHasType packHasType bodyHasType canShift)
                                               (No contra) => Left "Type of unpack must not have free variables"

export
Uninhabited (HasType emptyContext (TmTAbs body) (TyArr a b)) where
  uninhabited (VarHasType x) impossible
  uninhabited (AbsHasType x) impossible
  uninhabited (AppHasType x y) impossible
  uninhabited (TAbsHasType x) impossible
  uninhabited (TAppHasType x) impossible
  uninhabited (PackHasType x) impossible
  uninhabited (UnpackHasType x y bodyCanShiftDown) impossible

export
Uninhabited (HasType emptyContext (TmPack ty term tyb) (TyArr a b)) where
  uninhabited (VarHasType x) impossible
  uninhabited (AbsHasType x) impossible
  uninhabited (AppHasType x y) impossible
  uninhabited (TAbsHasType x) impossible
  uninhabited (TAppHasType x) impossible
  uninhabited (PackHasType x) impossible
  uninhabited (UnpackHasType x y bodyCanShiftDown) impossible

export
Uninhabited (HasType emptyContext (TmAbs ty body) (TyAll bTy)) where
  uninhabited (VarHasType x) impossible
  uninhabited (AbsHasType x) impossible
  uninhabited (AppHasType x y) impossible
  uninhabited (TAbsHasType x) impossible
  uninhabited (TAppHasType x) impossible
  uninhabited (PackHasType x) impossible
  uninhabited (UnpackHasType x y bodyCanShiftDown) impossible

export
Uninhabited (HasType emptyContext (TmPack aTy body pType) (TyAll bTy)) where
  uninhabited (VarHasType x) impossible
  uninhabited (AbsHasType x) impossible
  uninhabited (AppHasType x y) impossible
  uninhabited (TAbsHasType x) impossible
  uninhabited (TAppHasType x) impossible
  uninhabited (PackHasType x) impossible
  uninhabited (UnpackHasType x y bodyCanShiftDown) impossible

export
Uninhabited (HasType emptyContext (TmAbs ty body) (TySome someTy)) where
  uninhabited (VarHasType x) impossible
  uninhabited (AbsHasType x) impossible
  uninhabited (AppHasType x y) impossible
  uninhabited (TAbsHasType x) impossible
  uninhabited (TAppHasType x) impossible
  uninhabited (PackHasType x) impossible
  uninhabited (UnpackHasType x y bodyCanShiftDown) impossible

export
Uninhabited (HasType emptyContext (TmTAbs body) (TySome someTy)) where
  uninhabited (VarHasType x) impossible
  uninhabited (AbsHasType x) impossible
  uninhabited (AppHasType x y) impossible
  uninhabited (TAbsHasType x) impossible
  uninhabited (TAppHasType x) impossible
  uninhabited (PackHasType x) impossible
  uninhabited (UnpackHasType x y bodyCanShiftDown) impossible

%hint
coerceRenaming : {contextA, contextB : Context m n} -> {term : Term m n} -> HasType contextA term ty -> Renaming contextA contextB -> HasType contextB term ty
coerceRenaming (VarHasType termHasTypeInContext) renaming = VarHasType (coerceTermHasTypeInContext termHasTypeInContext renaming)
coerceRenaming (AbsHasType bodyHasType) renaming = AbsHasType {name=""} (coerceRenaming bodyHasType (addTerms renaming))
coerceRenaming (AppHasType funcHasType argHasType {tArg}) renaming = AppHasType {tArg} (coerceRenaming funcHasType renaming) (coerceRenaming argHasType renaming)
coerceRenaming (TAbsHasType bodyHasType) renaming = TAbsHasType {name=""} (coerceRenaming bodyHasType (addTypes renaming))
coerceRenaming (TAppHasType funcHasType) renaming = TAppHasType (coerceRenaming funcHasType renaming)
coerceRenaming (PackHasType bodyHasType) renaming = PackHasType (coerceRenaming bodyHasType renaming)
coerceRenaming (UnpackHasType packHasType bodyHasType bodyCanShiftDown {packType}) renaming =
  UnpackHasType {packType} {tyName=""} {tmName=""} (coerceRenaming packHasType renaming) (coerceRenaming bodyHasType (addTerms (addTypes renaming))) bodyCanShiftDown

export
hasTypeSameContextVarIsSameType : (context : Context m n) -> (term : Term m n) -> (tyA, tyB : Ty n) -> (a : HasType context term tyA) -> (b : HasType context term tyB) -> tyA = tyB
hasTypeSameContextVarIsSameType context (TmVar x) tyA tyB (VarHasType a) (VarHasType b) = sameTermHasSameType x context tyA tyB a b
hasTypeSameContextVarIsSameType context (TmAbs ty body) (TyArr ty aTy) (TyArr ty bTy) (AbsHasType a {name=aName}) (AbsHasType b) =
  cong (TyArr ty) (hasTypeSameContextVarIsSameType (addTermBinding context aName ty) body aTy bTy a (coerceRenaming b (addTerms reflexive)))
hasTypeSameContextVarIsSameType context (TmApp func arg) tyA tyB (AppHasType funcA argA {tArg=tArgA}) (AppHasType funcB argB {tArg=tArgB}) =
  snd (tyArrBiinjective $ hasTypeSameContextVarIsSameType context func (TyArr tArgA tyA) (TyArr tArgB tyB) funcA funcB)
hasTypeSameContextVarIsSameType context (TmTAbs body) (TyAll tyA) (TyAll tyB) (TAbsHasType a {name}) (TAbsHasType b) =
  cong TyAll (hasTypeSameContextVarIsSameType (addTypeBinding context name) body tyA tyB a (coerceRenaming b (addTypes reflexive)))
hasTypeSameContextVarIsSameType context (TmTApp func tArg) (substituteFirst tArg tyA) (substituteFirst tArg tyB) (TAppHasType a) (TAppHasType b) =
  cong (substituteFirst tArg) $ injective {f=TyAll} (hasTypeSameContextVarIsSameType context func (TyAll tyA) (TyAll tyB) a b)
hasTypeSameContextVarIsSameType context (TmPack tyArg body (TySome someTy)) (TySome someTy) (TySome someTy) (PackHasType a) (PackHasType b) = Refl
hasTypeSameContextVarIsSameType context (TmUnpack pack body) (shiftDown bodyTypeA FZ bodyCanShiftA) (shiftDown bodyTypeB FZ bodyCanShiftB)
                                (UnpackHasType {packType=packTyA} {tyName=tyNameA} {tmName=tmNameA} packA bodyA bodyCanShiftA) (UnpackHasType {packType=packTyB} {tyName=tyNameB} {tmName=tmNameB} packB bodyB bodyCanShiftB) =
  let packTypesEq = injective {f=TySome} $ hasTypeSameContextVarIsSameType context pack (TySome packTyA) (TySome packTyB) packA packB
      bodyTypesEq = hasTypeSameContextVarIsSameType ?ccon body bodyTypeA bodyTypeB bodyA (rewrite packTypesEq in coerceRenaming bodyB (addTerms (addTypes reflexive)))
   in rewrite bodyTypesEq in shiftDownSameIsSame bodyTypeB FZ _ _
