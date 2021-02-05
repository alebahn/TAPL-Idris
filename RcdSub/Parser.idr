module Parser

import Data.Strings
import Data.Vect
import Decidable.Equality
import Data.Nat
import Control.WellFounded
import Data.List1
import Data.DPair
import Data.List
import Data.So

import Tokens

%default total

Smaller : Char -> Char -> Type
Smaller x y = So (x < y)

smallerAndLargerAbsurd : {0 a, b : Char} -> a `Smaller` b -> b `Smaller`a -> Void
smallerAndLargerAbsurd x y = believe_me ()

soUnique : {0 a : Bool} -> (x, y : So a) -> x = y
soUnique Oh Oh = Refl

smallerToNotEqual : {0 a, b : Char} -> a `Smaller` b -> Not (a = b)
smallerToNotEqual x prf = believe_me ()

decSo : (x : Bool) -> Dec (So x)
decSo True = Yes Oh
decSo False = No uninhabited

decSmaller : (x, y : Char) -> Dec (Smaller x y)
decSmaller x y = decSo (x < y)

namespace CharList
  public export
  data SortsBefore : List Char -> List Char -> Type where
    EmptyBeforeNonEmpty : SortsBefore [] (x :: xs)
    SmallerCharSortsBefore : x `Smaller` y -> SortsBefore (x :: xs) (y :: ys)
    PrefixSortsBefore : SortsBefore xs ys -> SortsBefore (x :: xs) (x :: ys)

  export
  beforeAndAfterAbsurd : {0 a, b : List Char} -> SortsBefore a b -> SortsBefore b a -> Void
  beforeAndAfterAbsurd EmptyBeforeNonEmpty EmptyBeforeNonEmpty impossible
  beforeAndAfterAbsurd EmptyBeforeNonEmpty (SmallerCharSortsBefore x) impossible
  beforeAndAfterAbsurd EmptyBeforeNonEmpty (PrefixSortsBefore x) impossible
  beforeAndAfterAbsurd (SmallerCharSortsBefore x) (SmallerCharSortsBefore y) = smallerAndLargerAbsurd x y
  beforeAndAfterAbsurd (SmallerCharSortsBefore x) (PrefixSortsBefore y) = smallerToNotEqual x Refl
  beforeAndAfterAbsurd (PrefixSortsBefore x) (SmallerCharSortsBefore y) = smallerToNotEqual y Refl
  beforeAndAfterAbsurd (PrefixSortsBefore x) (PrefixSortsBefore y) = beforeAndAfterAbsurd x y

  export
  sortsBeforeUnique : {0 a, b : List Char} -> (x, y : SortsBefore a b) -> x = y
  sortsBeforeUnique EmptyBeforeNonEmpty EmptyBeforeNonEmpty = Refl
  sortsBeforeUnique (SmallerCharSortsBefore x) (SmallerCharSortsBefore y) = cong SmallerCharSortsBefore (soUnique x y)
  sortsBeforeUnique (SmallerCharSortsBefore x) (PrefixSortsBefore y) = void $ smallerToNotEqual x Refl
  sortsBeforeUnique (PrefixSortsBefore x) (SmallerCharSortsBefore y) = void $ smallerToNotEqual y Refl
  sortsBeforeUnique (PrefixSortsBefore x) (PrefixSortsBefore y) = cong PrefixSortsBefore $ sortsBeforeUnique x y

  export
  sortsBeforeToNotEqual : {0 a, b : List Char} -> SortsBefore a b -> Not (a = b)
  sortsBeforeToNotEqual EmptyBeforeNonEmpty prf = uninhabited prf
  sortsBeforeToNotEqual (SmallerCharSortsBefore charSmaller) Refl = smallerToNotEqual charSmaller Refl
  sortsBeforeToNotEqual (PrefixSortsBefore subABeforeSubB) Refl = sortsBeforeToNotEqual subABeforeSubB Refl

  Uninhabited (SortsBefore x []) where
    uninhabited EmptyBeforeNonEmpty impossible
    uninhabited (SmallerCharSortsBefore x) impossible
    uninhabited (PrefixSortsBefore x) impossible

  prefixNotBeforeNotBefore : (notSortsBefore : SortsBefore xs ys -> Void) -> SortsBefore (x :: xs) (x :: ys) -> Void
  prefixNotBeforeNotBefore _ (SmallerCharSortsBefore smaller) = smallerToNotEqual smaller Refl
  prefixNotBeforeNotBefore notSortsBefore (PrefixSortsBefore smaller) = notSortsBefore smaller

  notSmallerNotPrefixNotBefore : {0 x, y : Char} -> (notSmaller : x `Smaller` y -> Void) -> (notEq : x = y -> Void) -> SortsBefore (x :: xs) (y :: ys) -> Void
  notSmallerNotPrefixNotBefore notSmaller notEq (SmallerCharSortsBefore smaller) = notSmaller smaller
  notSmallerNotPrefixNotBefore notSmaller notEq (PrefixSortsBefore _) = notEq Refl

  export
  decSortsBefore : (x, y : List Char) -> Dec (SortsBefore x y)
  decSortsBefore [] (x :: xs) = Yes EmptyBeforeNonEmpty
  decSortsBefore x [] = No uninhabited
  decSortsBefore (x :: xs) (y :: ys) with (decSmaller x y)
    decSortsBefore (x :: xs) (y :: ys) | (Yes prf) = Yes (SmallerCharSortsBefore prf)
    decSortsBefore (x :: xs) (y :: ys) | (No notSmaller) with (decEq x y)
      decSortsBefore (x :: xs) (x :: ys) | (No notSmaller) | (Yes Refl) with (decSortsBefore xs ys)
        decSortsBefore (x :: xs) (x :: ys) | (No notSmaller) | (Yes Refl) | (Yes prf) = Yes (PrefixSortsBefore prf)
        decSortsBefore (x :: xs) (x :: ys) | (No notSmaller) | (Yes Refl) | (No notSortsBefore) = No (prefixNotBeforeNotBefore notSortsBefore)
      decSortsBefore (x :: xs) (y :: ys) | (No notSmaller) | (No notEq) = No (notSmallerNotPrefixNotBefore notSmaller notEq)

SortsBefore : String -> String -> Type
SortsBefore x y = SortsBefore (unpack x) (unpack y)

sortsBeforeToNotEqual : {0 a, b : String} -> SortsBefore a b -> Not (a = b)
sortsBeforeToNotEqual x prf = sortsBeforeToNotEqual x (cong unpack prf)

decSortsBefore : (x, y : String) -> Dec (SortsBefore x y)
decSortsBefore x y = decSortsBefore (unpack x) (unpack y)

NEQ : String -> String -> Type
NEQ x y = Either (SortsBefore x y) (SortsBefore y x)

neqUnique : {0 a, b : String} -> (x, y : NEQ a b) -> x = y
neqUnique (Left x) (Left y) = cong Left $ sortsBeforeUnique x y
neqUnique (Left x) (Right y) = void $ beforeAndAfterAbsurd x y
neqUnique (Right x) (Left y) = void $ beforeAndAfterAbsurd x y
neqUnique (Right x) (Right y) = cong Right $ sortsBeforeUnique x y

neqToNotEqual : NEQ a b -> Not (a = b)
neqToNotEqual (Left aBeforeB) prf = sortsBeforeToNotEqual aBeforeB prf
neqToNotEqual (Right bBeforeA) prf = sortsBeforeToNotEqual bBeforeA (sym prf)

notLeftNotRightNotEither : (notLeft : a -> Void) -> (notRight : b -> Void) -> (Either a b -> Void)
notLeftNotRightNotEither notLeft _ (Left x) = notLeft x
notLeftNotRightNotEither _ notRight (Right x) = notRight x

decNeq : (x, y : String) -> Dec (NEQ x y)
decNeq x y with (decSortsBefore x y)
  decNeq x y | (Yes prf) = Yes (Left prf)
  decNeq x y | (No notLeft) with (decSortsBefore y x)
    decNeq x y | (No notLeft) | (Yes prf) = Yes (Right prf)
    decNeq x y | (No notLeft) | (No notRight) = No (notLeftNotRightNotEither notLeft notRight)

mutual
  public export
  data BindingKeys : Type where
    EmptySet : BindingKeys
    AddElement : (newVal : String) -> (set : BindingKeys) -> (valIsNew : SetMissing newVal set) -> BindingKeys

  public export
  data SetMissing : String -> BindingKeys -> Type where
    EmptyMissing : SetMissing val EmptySet
    ConsMissing : (elem : String) -> (head : String) -> (elemNotHead : elem `NEQ` head) -> (elemNotInTail : SetMissing elem tail) -> {existingSetMissing : SetMissing head tail} -> SetMissing elem (AddElement head tail existingSetMissing)

public export
length : BindingKeys -> Nat
length EmptySet = 0
length (AddElement _ set _) = S (length set)

emptyNotAdd : {0 x : String} -> {0 y : BindingKeys} -> {0 z : SetMissing x y} -> EmptySet = AddElement x y z -> Void
emptyNotAdd Refl impossible

public export
data InBounds : (k : Nat) -> (set : BindingKeys) -> Type where
  InFirst : InBounds Z (AddElement head set headIsNew)
  InLater : InBounds k set -> InBounds (S k) (AddElement head set headIsNew)

export
index : (n : Nat) -> (set : BindingKeys) -> {auto 0 ok : InBounds n set} -> String
index 0 (AddElement head _ _) {ok = InFirst} = head
index (S k) (AddElement head set headIsNew) {ok = (InLater ok)} = index k set

export
getIndex : (name : String) -> (set : BindingKeys) -> Maybe (n : Nat ** inBounds : InBounds n set ** name = index n set)
getIndex name EmptySet = Nothing
getIndex name (AddElement head tail _) = case decEq name head of
                                               (Yes prf) => Just (Z ** InFirst ** prf)
                                               (No _) => do (n ** inBounds ** isIndex) <- getIndex name tail
                                                            Just (S n ** InLater inBounds ** isIndex)

export
inBoundsToFinLength: (n : Nat) -> {0 set : BindingKeys} -> {auto 0 ok : InBounds n set} -> Fin (length set)
inBoundsToFinLength 0 {ok = InFirst} = FZ
inBoundsToFinLength (S k) {ok = (InLater ok)} = FS (inBoundsToFinLength k)

valIsNewIsUnique : (valIsNewA, valIsNewB : SetMissing newVal set) -> valIsNewA = valIsNewB
valIsNewIsUnique EmptyMissing EmptyMissing = Refl
valIsNewIsUnique (ConsMissing newVal head newNotHeadA newNotInTailA) (ConsMissing newVal head newNotHeadB newNotInTailB) = rewrite the (newNotHeadA = newNotHeadB) (neqUnique newNotHeadA newNotHeadB) in rewrite valIsNewIsUnique newNotInTailA newNotInTailB in Refl

DecEq BindingKeys where
  decEq EmptySet EmptySet = Yes Refl
  decEq EmptySet (AddElement newVal set valIsNew) = No emptyNotAdd
  decEq (AddElement newVal set valIsNew) EmptySet = No (\eq => emptyNotAdd $ sym eq)
  decEq (AddElement newValA setA valIsNewA) (AddElement newValB setB valIsNewB) with (decEq newValA newValB)
    decEq (AddElement newValA setA valIsNewA) (AddElement newValB setB valIsNewB) | (No contra) = No (\Refl => contra Refl)
    decEq (AddElement newVal setA valIsNewA) (AddElement newVal setB valIsNewB) | (Yes Refl) with (decEq setA setB)
      decEq (AddElement newVal setA valIsNewA) (AddElement newVal setB valIsNewB) | (Yes Refl) | (No contra) = No (\Refl => contra Refl)
      decEq (AddElement newVal set valIsNewA) (AddElement newVal set valIsNewB) | (Yes Refl) | (Yes Refl) = Yes (rewrite valIsNewIsUnique valIsNewA valIsNewB in Refl)

decSetMissing : (elem : String) -> (set : BindingKeys) -> Dec (SetMissing elem set)
decSetMissing elem EmptySet = Yes EmptyMissing
decSetMissing elem (AddElement newVal set valIsNew) with (decNeq elem newVal)
  decSetMissing elem (AddElement newVal set valIsNew) | (Yes neqHead) with (decSetMissing elem set)
    decSetMissing elem (AddElement newVal set valIsNew) | (Yes neqHead) | (Yes notInTail) = Yes (ConsMissing elem newVal neqHead notInTail)
    decSetMissing elem (AddElement newVal set valIsNew) | (Yes neqHead) | (No contra) = No (\(ConsMissing _ _ _ notInTail) => contra notInTail)
  decSetMissing elem (AddElement newVal set valIsNew) | (No contra) = No (\(ConsMissing _ _ neqHead _) => contra neqHead)

public export
record RecordMap (v : Type) where
  constructor MkRecordMap
  keys : BindingKeys
  values : Vect (length keys) v

DecEq v => DecEq (RecordMap v) where
  decEq (MkRecordMap keysA valuesA) (MkRecordMap keysB valuesB) with (decEq keysA keysB)
    decEq (MkRecordMap keysA valuesA) (MkRecordMap keysB valuesB) | (No contra) = No (\Refl => contra Refl)
    decEq (MkRecordMap keys valuesA) (MkRecordMap keys valuesB) | (Yes Refl) with (decEq valuesA valuesB)
      decEq (MkRecordMap keys values) (MkRecordMap keys values) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (MkRecordMap keys valuesA) (MkRecordMap keys valuesB) | (Yes Refl) | (No contra) = No (\Refl => contra Refl)

public export
Functor RecordMap where
  map f (MkRecordMap keys values) = MkRecordMap keys (f <$> values)

public export
data Ty = TyRec (RecordMap Ty) | TyArr Ty Ty

recNotArr : TyRec a = TyArr x y -> Void
recNotArr Refl impossible

mutual
  decEqImpl_VecTy : (a, b : Vect n Ty) -> Dec (a = b)
  decEqImpl_VecTy [] [] = Yes Refl
  decEqImpl_VecTy (x :: xs) (y :: ys) with (decEqImpl_Ty x y)
    decEqImpl_VecTy (x :: xs) (y :: ys) | (No contra) = No (\Refl => contra Refl)
    decEqImpl_VecTy (x :: xs) (x :: ys) | (Yes Refl) with (decEqImpl_VecTy xs ys)
      decEqImpl_VecTy (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEqImpl_VecTy (x :: xs) (x :: ys) | (Yes Refl) | (No contra) = No (\Refl => contra Refl)

  decEqImpl_TyRec : (a, b : RecordMap Ty) -> Dec (a = b)
  decEqImpl_TyRec (MkRecordMap keysA valuesA) (MkRecordMap keysB valuesB) with (decEq keysA keysB)
    decEqImpl_TyRec (MkRecordMap keysA valuesA) (MkRecordMap keysB valuesB) | (No contra) = No (\Refl => contra Refl)
    decEqImpl_TyRec (MkRecordMap keys valuesA) (MkRecordMap keys valuesB) | (Yes Refl) with (decEqImpl_VecTy valuesA valuesB)
      decEqImpl_TyRec (MkRecordMap keys values) (MkRecordMap keys values) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEqImpl_TyRec (MkRecordMap keys valuesA) (MkRecordMap keys valuesB) | (Yes Refl) | (No contra) = No (\Refl => contra Refl)

  decEqImpl_Ty : (a, b : Ty) -> Dec (a = b)
  decEqImpl_Ty (TyRec a) (TyRec b) with (decEqImpl_TyRec a b)
    decEqImpl_Ty (TyRec a) (TyRec a) | (Yes Refl) = Yes Refl
    decEqImpl_Ty (TyRec a) (TyRec b) | (No contra) = No (\Refl => contra Refl)
  decEqImpl_Ty (TyArr w x) (TyArr y z) with (decEqImpl_Ty w y)
    decEqImpl_Ty (TyArr w x) (TyArr w z) | (Yes Refl) with (decEqImpl_Ty x z)
      decEqImpl_Ty (TyArr w x) (TyArr w x) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEqImpl_Ty (TyArr w x) (TyArr w z) | (Yes Refl) | (No contra) = No (\Refl => contra Refl)
    decEqImpl_Ty (TyArr w x) (TyArr y z) | (No contra) = No (\Refl => contra Refl)
  decEqImpl_Ty (TyRec _) (TyArr _ _) = No recNotArr
  decEqImpl_Ty (TyArr _ _) (TyRec _) = No (\eq => (recNotArr $ sym eq))

export
DecEq Ty where
  decEq = decEqImpl_Ty

mutual
  public export
  data Term : Nat -> Type where
    TmVar : Fin n -> Term n
    TmAbs : (nm : String) -> (ty : Ty )-> (body : Term (S n)) -> Term n
    TmApp : Term n -> Term n -> Term n
    TmRec : RecordMap (Term n) -> Term n
    TmProj : Term n -> (name : String) -> Term n

public export
Context : Nat ->Type
Context n = Vect n (String, Ty)

public export
addBinding : Context n -> (name : String) -> Ty -> Context (S n)
addBinding context name ty = (name, ty) :: context

public export
getBindingType : Context n -> Fin n -> Ty
getBindingType context i = snd (index i context)

absPrec : Prec
absPrec = User 0

projPrec : Prec
projPrec = User 1

appLhsPrec : Prec
appLhsPrec = User 2

appRhsPrec : Prec
appRhsPrec = User 3

joinWith : String -> List String -> String
joinWith glue [] = ""
joinWith glue (x :: xs) = foldl (++) x ((glue ++) <$> xs)

mutual

  showRecord : Context n -> RecordMap (Term n) -> List String
  showRecord context (MkRecordMap keys values) = showRecord' context keys values
    where
      showRecord' : Context n -> (keys : BindingKeys) -> (values : Vect (length keys) (Term n)) -> List String
      showRecord' context EmptySet [] = []
      showRecord' context (AddElement newVal set _) (val :: vals) = (newVal ++ " = " ++ showPrec Open context val) :: showRecord' context set vals

  showPrec : Prec -> Context n -> Term n -> String
  showPrec _ context (TmVar j) = fst (index j context)
  showPrec d context (TmAbs name ty body) = showParens (d > absPrec) ("\\" ++ name ++ ". " ++ showPrec absPrec (addBinding context name ty) body)
  showPrec d context (TmApp x y) = showParens (d >= appRhsPrec) (showPrec appLhsPrec context x ++ " " ++ showPrec appRhsPrec context y)
  showPrec _ context (TmRec recordMap) = "{" ++ joinWith ", " (showRecord context recordMap) ++ "}"
  showPrec d context (TmProj x y) = showParens (d > projPrec) (showPrec projPrec context x ++ "." ++ y)

export
show : Context n -> Term n -> String
show context term = showPrec Open context term

mutual
  parseRecTy: (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (RecordMap Ty, Subset (List Token) (\resid => resid `Smaller` tokens))
  parseRecTy (TVar name :: TColon :: xs) (Access acc) = do (ty, Element resid residSmaller) <- parseType xs (acc xs (lteSuccRight lteRefl))
                                                           case resid of
                                                                (TComma :: ys) => do (MkRecordMap keys types, Element resid' residSmaller') <- parseRecTy ys (acc ys (lteSuccLeft $ lteSuccRight $ lteSuccRight residSmaller))
                                                                                     case decSetMissing name keys of
                                                                                          (Yes prf) => Right (MkRecordMap (AddElement name keys prf) (ty :: types), Element resid' (lteTransitive residSmaller' (lteSuccLeft $ lteSuccLeft $ lteSuccRight $ lteSuccRight residSmaller)))
                                                                                          (No _) => Left ("Duplicate label in record : " ++ name)
                                                                (TRBrace :: ys) => Right (MkRecordMap (AddElement name EmptySet EmptyMissing) [ty], Element ys (lteSuccLeft $ lteSuccRight $ lteSuccRight residSmaller))
                                                                _ => Left "Expected '}' or ','"
  parseRecTy _ _ = Left "Expected record type binding"

  parsePartType : (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (Ty, (Subset (List Token) (\resid => resid `Smaller` tokens)))
  parsePartType (TLBrace :: TRBrace :: xs) _ = Right (TyRec (MkRecordMap EmptySet []), Element xs (lteSuccRight lteRefl))
  parsePartType (TLBrace :: xs) (Access acc) = do (recordMap, (Element resid residSmaller)) <- parseRecTy xs (acc xs lteRefl)
                                                  Right (TyRec recordMap, (Element resid (lteSuccRight residSmaller)))
  parsePartType (TLParen :: xs) (Access acc) = do (ty, (Element (TRParen :: resid) residSmaller)) <- parseType xs (acc xs lteRefl)
                                                    | _ => Left "Expected ')'"
                                                  pure (ty, (Element resid (lteSuccLeft $ lteSuccRight residSmaller)))
  parsePartType _ _ = Left "Invalid type"

  parseType : (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (Ty, (Subset (List Token) (\resid => resid `Smaller` tokens)))
  parseType tokens (Access acc) = do (ty, (Element resid residSmaller)) <- parsePartType tokens (Access acc)
                                     case resid of
                                          (TArrow :: xs) => do (tyRight, (Element resid' residSmaller')) <- parseType xs (acc xs (lteSuccLeft residSmaller))
                                                               pure (TyArr ty tyRight, (Element resid' (lteTransitive residSmaller' (lteSuccLeft $ lteSuccLeft residSmaller))))
                                          xs => Right (ty, (Element xs residSmaller))

ParseResult : Nat -> List Token -> Type
ParseResult n tokens = (Term n, (Subset (List Token) (\resid => resid `Smaller` tokens)))

mutual
  parseTerms : {n : Nat} -> (context : Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (List1 (Term n), (Subset (List Token) (\resid => resid `Smaller` tokens)))
  parseTerms context tokens (Access acc) = do (term, (Element resid residSmaller)) <- parseMaybeProj context tokens (Access acc)
                                              case parseTerms context resid (acc resid residSmaller) of
                                                   (Left _) => Right (term ::: [], (Element resid residSmaller))
                                                   (Right (terms, (Element resid' residSmaller'))) => Right (term ::: (forget terms), (Element resid' (lteTransitive residSmaller' (lteSuccLeft residSmaller))))

  parseWhole : {n : Nat} -> (context : Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (ParseResult n tokens)
  parseWhole context tokens acc = do (terms, resid) <- parseTerms context tokens acc
                                     Right (foldl1 id TmApp terms, resid)

  parseProjs : (tokens : List Token) -> Maybe (List1 String, Subset (List Token) (\resid => resid `Smaller` tokens))
  parseProjs (TDot :: TVar name :: xs) = case parseProjs xs of
                                              Nothing => Just (name ::: [], Element xs (lteSuccRight lteRefl))
                                              (Just (projections, Element resid residSmaller)) => Just (name ::: forget projections, Element resid (lteSuccRight $ lteSuccRight residSmaller))
  parseProjs _ = Nothing

  parseMaybeProj : {n : Nat} -> (context : Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (ParseResult n tokens)
  parseMaybeProj context tokens acc = do (term, Element resid residSmaller) <- parseTerm context tokens acc
                                         case parseProjs resid of
                                              Nothing => Right (term, Element resid residSmaller)
                                              (Just (projections, Element resid' residSmaller')) => Right (foldl TmProj term projections, Element resid' (lteTransitive residSmaller' (lteSuccLeft residSmaller)))

  parseRecord : {n : Nat} -> (context : Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (RecordMap (Term n), Subset (List Token) (\resid => resid `Smaller` tokens))
  parseRecord context (TVar name :: TEqual :: xs) (Access acc) = do (term, Element resid residSmaller) <- parseWhole context xs (acc xs (lteSuccRight lteRefl))
                                                                    case resid of
                                                                         (TComma :: ys) => do (MkRecordMap keys terms, Element resid' residSmaller') <- parseRecord context ys (acc ys (lteSuccLeft $ lteSuccRight $ lteSuccRight residSmaller))
                                                                                              case decSetMissing name keys of
                                                                                                   (Yes prf) => Right (MkRecordMap (AddElement name keys prf) (term :: terms), Element resid' (lteTransitive residSmaller' (lteSuccLeft $ lteSuccLeft $ lteSuccRight $ lteSuccRight residSmaller)))
                                                                                                   (No _) => Left ("Duplicate label in record : " ++ name)
                                                                         (TRBrace :: ys) => Right (MkRecordMap (AddElement name EmptySet EmptyMissing) [term], Element ys (lteSuccLeft $ lteSuccRight $ lteSuccRight residSmaller))
                                                                         _ => Left "Expected '}' or ','"
  parseRecord _ _ _ = Left "Expected record binding"

  parseTerm : {n : Nat} -> (context : Context n) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (ParseResult n tokens)
  parseTerm context ((TVar name) :: xs) (Access acc) = case findIndex ((== name) . fst) context of
                                                            Nothing => Left (name ++ " is not bound")
                                                            (Just idx) => Right (TmVar idx, (Element xs lteRefl))
  parseTerm context (TLambda :: (TVar name) :: TColon :: xs) (Access acc) = do (type, (Element (TDot :: ys) residSmaller)) <- parseType xs (acc xs (lteSuccRight $ lteSuccRight $ lteRefl))
                                                                                | _ => Left "Expected '.'"
                                                                               (body, (Element resid residSmaller')) <- parseWhole (addBinding context name type) ys (acc ys (lteSuccLeft $ lteSuccRight $ lteSuccRight $ lteSuccRight residSmaller))
                                                                               pure (TmAbs name type body, (Element resid (lteTransitive residSmaller' (lteSuccLeft $ lteSuccLeft $ lteSuccRight $ lteSuccRight $ lteSuccRight residSmaller))))
  parseTerm context (TLParen :: xs) (Access acc) = do (term, (Element (TRParen :: resid) residSmaller)) <- parseWhole context xs (acc xs lteRefl)
                                                       | _ => Left "Expected ')'"
                                                      Right (term, (Element resid (lteSuccLeft $ lteSuccRight residSmaller)))
  parseTerm context (TLBrace :: TRBrace :: xs) _ = Right (TmRec (MkRecordMap EmptySet []),  Element xs (lteSuccRight lteRefl))
  parseTerm context (TLBrace :: xs) (Access acc) = do (termRecord, Element resid residSmaller) <- parseRecord context xs (acc xs lteRefl)
                                                      Right (TmRec termRecord, Element resid (lteSuccRight residSmaller))
  parseTerm _ _ _ = Left "Invalid Term"

export
parse : String -> Either String (Term 0)
parse str = do
  tokens <- tokenize str
  (term, (Element [] _)) <- parseWhole [] tokens (sizeAccessible tokens)
    | _ => Left "Extra tokens at end of term"
  pure term
