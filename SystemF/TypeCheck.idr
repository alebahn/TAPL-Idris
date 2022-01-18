module TypeCheck

import Context
import Term
import Ty

import Decidable.Equality

%default total

public export
data HasType : {m, n : Nat} -> Context m n -> Term m n -> Ty n -> Type where
  VarHasType : TermHasTypeInContext ind ty context -> HasType context (TmVar ind) ty
  AbsHasType : HasType (addTermBinding context name ty) body bTy -> HasType context (TmAbs ty body) (TyArr ty bTy)
  AppHasType : HasType context func (TyArr tArg tRes) -> HasType context arg tArg -> HasType context (TmApp func arg) tRes
  TAbsHasType : HasType (addTypeBinding context name) body bTy -> HasType context (TmTAbs body) (TyAll bTy)
  TAppHasType : HasType context uni (TyAll bTy) -> HasType context (TmTApp uni arg) (substituteFirst arg bTy)
  PackHasType : HasType context some (substituteFirst ty someTy) -> HasType context (TmPack ty some (TySome someTy)) (TySome someTy)
  UnpackHasType : HasType context package (TySome packType) -> HasType (addTermBinding (addTypeBinding context tyName) tmName packType) body bodyType -> (bodyCanShiftDown : CanShiftDown FZ bodyType) -> HasType context (TmUnpack package body) (shiftDown bodyType FZ bodyCanShiftDown)

hasType : (context : Context m n) -> (term : Term m n) -> Either String (ty : Ty n ** HasType context term ty)
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
