module Parser

import Data.Vect
import Data.Nat
import Control.WellFounded
import Data.List1
import Data.DPair

import Tokens
import Terms

%default total

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
  parsePartType (TTop :: xs) _ = Right (TyTop, Element xs lteRefl)
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
