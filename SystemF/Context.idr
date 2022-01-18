module Context

import public Data.Fin
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

export
data TermHasTypeInContext : Fin m-> Ty n -> Context m n -> Type where
  TermFirst : TermHasTypeInContext FZ ty (AddTerm name ty context)
  TermLater : TermHasTypeInContext ind ty context -> TermHasTypeInContext (FS ind) ty (AddTerm name ty2 context)
  AfterTy : {0 m, n : Nat} -> {ind : Fin m} -> {ty : Ty n} -> {context : Context m n} -> {name : String} -> TermHasTypeInContext ind ty context ->
            TermHasTypeInContext ind (shiftUpBase ty 1) (AddType name context)

export
getTermBindingType : (context : Context n m) -> (ind : Fin n) -> (ty : Ty m ** TermHasTypeInContext ind ty context)
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
