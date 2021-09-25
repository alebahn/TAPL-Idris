module Recon

import Data.Fin
import Data.Vect
import Data.Stream

%default total

data Ty = TyBool | TyArr Ty Ty | TyId String | TyNat

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
