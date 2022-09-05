module Context

import public Data.Fin
import Data.Vect.Quantifiers
import Decidable.Equality

import Ty

%default total

public export
data Context : Nat -> Nat -> Type where
  EmptyContext : Context 0 0
  AddTerm : (name : String) -> Ty m -> Context n m -> Context (S n) m
  AddType : (name : String) -> Context n m -> Context n (S m)

export
emptyContext : Context 0 0
emptyContext = EmptyContext

export
addTermBinding : Context n m -> (name : String) -> Ty m -> Context (S n) m
addTermBinding context name ty = AddTerm name ty context

export
addTypeBinding : Context n m -> (name : String) -> Context n (S m)
addTypeBinding context name = AddType name context

public export
data TermHasTypeInContext : Fin m-> Ty n -> Context m n -> Type where
  TermFirst : TermHasTypeInContext FZ ty (AddTerm name ty context)
  TermLater : TermHasTypeInContext ind ty context -> TermHasTypeInContext (FS ind) ty (AddTerm name ty2 context)
  AfterTy : {0 m, n : Nat} -> {ind : Fin m} -> {ty : Ty n} -> {context : Context m n} -> {name : String} -> TermHasTypeInContext ind ty context ->
            TermHasTypeInContext ind (shiftUpBase ty 1) (AddType name context)

export
sameTermHasSameType : (var : Fin m) -> (context : Context m n) -> (tyA, tyB : Ty n) -> (a : TermHasTypeInContext var tyA context) -> (b : TermHasTypeInContext var tyB context) -> tyA = tyB
sameTermHasSameType FZ (AddTerm name _ context) tyA tyA TermFirst TermFirst = Refl
sameTermHasSameType (FS var) (AddTerm name ty2 context) tyA tyB (TermLater a) (TermLater b) = sameTermHasSameType var context tyA tyB a b
sameTermHasSameType var (AddType name context) (shiftUpBase ty 1) (shiftUpBase ty 1) (AfterTy a) (AfterTy b) = Refl

export
getTermBindingType : {m : _} -> (context : Context n m) -> (ind : Fin n) -> (ty : Ty m ** TermHasTypeInContext ind ty context)
getTermBindingType EmptyContext ind = absurd ind
getTermBindingType (AddTerm name ty tail) FZ = (ty ** TermFirst)
getTermBindingType (AddTerm name ty tail) (FS ind) = let (ty ** prf) = getTermBindingType tail ind
                                                      in (ty ** TermLater prf)
getTermBindingType (AddType name tail) ind = let (ty ** prf) = getTermBindingType tail ind
                                              in (shiftUpBase ty 1 ** AfterTy prf)

export
getTermBindingName : Context n m -> Fin n -> String
getTermBindingName EmptyContext ind = absurd ind
getTermBindingName (AddTerm name _ _   ) FZ = name
getTermBindingName (AddTerm _    _ tail) (FS ind) = getTermBindingName tail ind
getTermBindingName (AddType _ tail) ind = getTermBindingName tail ind

export
getTypeBindingName : Context n m -> Fin m -> String
getTypeBindingName EmptyContext ind = absurd ind
getTypeBindingName (AddTerm _ _ tail) ind = getTypeBindingName tail ind
getTypeBindingName (AddType name _   ) FZ = name
getTypeBindingName (AddType _    tail) (FS ind) = getTypeBindingName tail ind

export
getTermIndex : Context n m -> String -> Maybe (Fin n)
getTermIndex EmptyContext search = Nothing
getTermIndex (AddTerm name _ tail) search with (decEq name search)
  getTermIndex (AddTerm name _ tail) search | (Yes prf) = Just FZ
  getTermIndex (AddTerm name _ tail) search | (No contra) = FS <$> (getTermIndex tail search)
getTermIndex (AddType name tail) search = getTermIndex tail search

export
getTypeIndex : Context n m -> String -> Maybe (Fin m)
getTypeIndex EmptyContext search = Nothing
getTypeIndex (AddTerm _ _ tail) search = getTypeIndex tail search
getTypeIndex (AddType name tail) search with (decEq name search)
  getTypeIndex (AddType name tail) search | (Yes prf) = Just FZ
  getTypeIndex (AddType name tail) search | (No contra) = FS <$> (getTypeIndex tail search)

public export
substituteContext : {l, m, n, p : Nat} ->
                    (contextFull : Context (l + m) (n + p)) ->
                    (substitutions : Tys p) ->
                    (Context l n)
substituteContext {l = 0} {n = 0} contextFull substitutions = EmptyContext
substituteContext {l = 0} {n = (S n)} (AddTerm _ _ contextFull) substitutions = substituteContext contextFull substitutions
substituteContext {l = 0} {n = (S n)} (AddType name contextFull) substitutions = AddType name (substituteContext contextFull substitutions)
substituteContext {l = (S l)} {n = 0} (AddTerm name ty contextFull) substitutions = AddTerm name ?newTy (substituteContext contextFull substitutions)
substituteContext {l = (S l)} {n = 0} (AddType name contextFull) (_ :: substitutions) = substituteContext contextFull substitutions
substituteContext {l = (S l)} {n = (S n)} (AddTerm name ty contextFull) substitutions = AddTerm name ?newTyy (substituteContext contextFull substitutions)
substituteContext {l = (S l)} {n = (S n)} (AddType name contextFull) substitutions = AddType name (substituteContext contextFull substitutions)

export
substituteContextNoneNeutral :{l,n : Nat} -> (contextFull : Context (l+0) (n+0)) -> (substituteContext {l} {m=0} {n} {p=0} contextFull []) = (rewrite sym $ plusZeroRightNeutral l in rewrite sym $ plusZeroRightNeutral n in contextFull)

export
data CanShiftDown : (ind : Fin (S m)) -> (context : Context n (S m)) -> Type where
  AddTermCanShiftDown : CanShiftDown ind ty -> CanShiftDown ind context -> CanShiftDown ind (AddTerm name ty context)
  AddTypeCanShiftDownFZ : CanShiftDown FZ (AddType name context)
  AddTypeCanShiftDownFS : CanShiftDown ind context -> CanShiftDown (FS ind) (AddType name context)

export
shiftDown : (ind : Fin (S m)) -> (context : Context n (S m)) -> CanShiftDown ind context -> Context n m
shiftDown ind (AddTerm name ty context) (AddTermCanShiftDown tyCanShiftDown contextCanShiftDown) = AddTerm name (shiftDown ty ind tyCanShiftDown) (shiftDown ind context contextCanShiftDown)
shiftDown FZ (AddType name context) AddTypeCanShiftDownFZ = context
shiftDown (FS ind) (AddType name context) (AddTypeCanShiftDownFS contextCanShiftDown) = AddType name (shiftDown ind context contextCanShiftDown)

export
%hint
addTermBindingCanShiftDown : CanShiftDown ind ty -> CanShiftDown ind context -> CanShiftDown ind (addTermBinding context name ty)
addTermBindingCanShiftDown = AddTermCanShiftDown

export
%hint
addTypeBindingCanShiftDown : CanShiftDown ind context -> CanShiftDown (FS ind) (addTypeBinding context name)
addTypeBindingCanShiftDown = AddTypeCanShiftDownFS

export
addTermBindingAndShiftDownCommute : (ind : Fin (S m)) -> (context : Context n (S m)) -> (canShiftDown : CanShiftDown ind context) -> (ty : Ty (S m)) -> (tyCanShift : CanShiftDown ind ty) ->
                                    (canShiftDown' : CanShiftDown ind (addTermBinding context name ty)
                                    ** addTermBinding (shiftDown ind context canShiftDown) name (shiftDown ty ind tyCanShift) = shiftDown ind (addTermBinding context name ty) canShiftDown')
addTermBindingAndShiftDownCommute ind (AddTerm name newTy context) (AddTermCanShiftDown newTyCanShiftDown contextCanShiftDown) ty tyCanShift =
  (AddTermCanShiftDown tyCanShift (AddTermCanShiftDown newTyCanShiftDown contextCanShiftDown) ** Refl)
addTermBindingAndShiftDownCommute FZ (AddType name context) AddTypeCanShiftDownFZ ty tyCanShift =
  (AddTermCanShiftDown tyCanShift AddTypeCanShiftDownFZ ** Refl)
addTermBindingAndShiftDownCommute (FS ind) (AddType name context) (AddTypeCanShiftDownFS contextCanShiftDown) ty tyCanShift =
  (AddTermCanShiftDown tyCanShift (AddTypeCanShiftDownFS contextCanShiftDown) ** Refl)

export
typeInContextCanShiftDown : {n : Nat} -> {ty : Ty (S n)} -> {0 context : Context m (S n)} -> {var : Fin (S n)} -> TermHasTypeInContext ind ty context -> CanShiftDown var context -> CanShiftDown var ty
typeInContextCanShiftDown TermFirst (AddTermCanShiftDown tyCanShift _) = tyCanShift
typeInContextCanShiftDown (TermLater termHasTypeInContext) (AddTermCanShiftDown _ contextCanShift) = typeInContextCanShiftDown termHasTypeInContext contextCanShift
typeInContextCanShiftDown (AfterTy termHasTypeInContext {ty}) AddTypeCanShiftDownFZ = shiftUpBaseCanShiftDown ty
typeInContextCanShiftDown {n = S n} (AfterTy termHasTypeInContext {ty} {ind}) (AddTypeCanShiftDownFS contextCanShift {ind=var}) {context = AddType name context} =
   canShiftDownToShiftUpBaseCanShiftDown var ty (typeInContextCanShiftDown termHasTypeInContext contextCanShift)

export
%hint
addTypeBindingCanShiftDownFZ : CanShiftDown FZ (addTypeBinding context name)
addTypeBindingCanShiftDownFZ = AddTypeCanShiftDownFZ

export
shiftDownAddTypeIsId : (context : Context n m) -> shiftDown FZ (addTypeBinding context name) Context.addTypeBindingCanShiftDownFZ = context
shiftDownAddTypeIsId EmptyContext = Refl
shiftDownAddTypeIsId (AddTerm name ty context) = Refl
shiftDownAddTypeIsId (AddType name context) = Refl

export
shiftDownAddTypeCommute : (context : Context n (S m)) -> (contextCanShiftDown :  CanShiftDown var context) -> addTypeBinding (shiftDown var context contextCanShiftDown) name = shiftDown (FS var) (addTypeBinding context name) (AddTypeCanShiftDownFS contextCanShiftDown)
shiftDownAddTypeCommute context contextCanShiftDown = Refl

export
shiftDownHasTyVar : {n : Nat} -> {0 context : Context m (S n)} -> {var : Fin (S n)} -> {0 ty : Ty (S n)} -> TermHasTypeInContext ind ty context -> (tyCanShiftDown : CanShiftDown var ty) -> (contextCanShiftDown : Context.CanShiftDown var context) -> TermHasTypeInContext ind (shiftDown ty var tyCanShiftDown) (shiftDown var context contextCanShiftDown)
shiftDownHasTyVar TermFirst tyCanShiftDown (AddTermCanShiftDown tyCanShiftDown' contextCanShiftDown) = rewrite shiftDownSameIsSame ty var tyCanShiftDown tyCanShiftDown' in TermFirst
shiftDownHasTyVar (TermLater termHasTypeInContext) tyCanShiftDown (AddTermCanShiftDown _ contextCanShiftDown) = TermLater (shiftDownHasTyVar termHasTypeInContext tyCanShiftDown contextCanShiftDown)
shiftDownHasTyVar {ty = shiftUpBase ty 1} (AfterTy termHasTypeInContext) tyCanShiftDown AddTypeCanShiftDownFZ = rewrite shiftDownShiftUpBaseIsId ty tyCanShiftDown in termHasTypeInContext
shiftDownHasTyVar {ty = shiftUpBase ty 1} {var = FS var} (AfterTy termHasTypeInContext) tyCanShiftDown (AddTypeCanShiftDownFS contextCanShiftDown) =
  let (tyCanShiftDown' ** eq) = shiftDownShiftUpBaseToShiftUpBaseShiftDown var ty tyCanShiftDown
   in rewrite eq in AfterTy $ shiftDownHasTyVar termHasTypeInContext tyCanShiftDown' contextCanShiftDown

export
data Renaming : Context n m -> Context n m -> Type where
  EmptyRenaming : Renaming EmptyContext EmptyContext
  AddTerms : Renaming ca cb -> Renaming (AddTerm nameA ty ca) (AddTerm nameB ty cb)
  AddTypes : Renaming ca cb -> Renaming (AddType nameA ca) (AddType nameB cb)

export
Reflexive (Context n m) Renaming where
  reflexive {x = EmptyContext} = EmptyRenaming
  reflexive {x = AddTerm name ty con} = AddTerms reflexive
  reflexive {x = AddType name con} = AddTypes reflexive

export
coerceTermHasTypeInContext : {contextA, contextB : Context m n} -> TermHasTypeInContext ind ty contextA -> Renaming contextA contextB -> TermHasTypeInContext ind ty contextB
coerceTermHasTypeInContext TermFirst (AddTerms _) = TermFirst
coerceTermHasTypeInContext (TermLater termHasTypeInContext) (AddTerms renaming) = TermLater (coerceTermHasTypeInContext termHasTypeInContext renaming)
coerceTermHasTypeInContext (AfterTy termHasTypeInContext) (AddTypes renaming) = AfterTy (coerceTermHasTypeInContext termHasTypeInContext renaming)

export
addTerms : Renaming ca cb -> Renaming (addTermBinding ca nameA ty) (addTermBinding cb nameB ty)
addTerms = AddTerms

export
addTypes : Renaming ca cb -> Renaming (addTypeBinding ca nameA) (addTypeBinding cb nameB)
addTypes = AddTypes
