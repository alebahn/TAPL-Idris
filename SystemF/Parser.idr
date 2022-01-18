module Parser

import Data.String
import Data.Vect
import Decidable.Equality
import Data.Nat
import Control.WellFounded
import Data.List1
import Data.DPair
import Data.Maybe
import Data.Either

import Tokens
import Ty
import Term
import Context

%default total

mutual
  parsePartType : (Context n m) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (Ty m, (Subset (List Token) (\resid => resid `Smaller` tokens)))
  parsePartType context (TVar l :: xs) acc = do ind <- maybeToEither ("Type variable '" ++ l ++ "' not found") (getTypeIndex context l)
                                                pure (TyVar ind, (Element xs (reflexive {rel=LTE})))
  parsePartType context (TLParen :: xs) (Access acc) = do (ty, (Element (TRParen :: resid) residSmaller)) <- parseType context xs (acc xs (reflexive {rel = LTE}))
                                                          | _ => Left "Expected ')'"
                                                          pure (ty, (Element resid (lteSuccLeft $ lteSuccRight residSmaller)))
  parsePartType _ _ _ = Left "Invalid type"

  parseType : (Context n m) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (Ty m, (Subset (List Token) (\resid => resid `Smaller` tokens)))
  parseType context (TForAll :: TVar l :: TDot :: xs) (Access acc) = do (ty, (Element resid residSmaller)) <- parseType (addTypeBinding context l) xs (acc xs (lteSuccRight $ lteSuccRight $ reflexive {rel=LTE}))
                                                                        pure (TyAll ty, (Element resid (transitive {rel=LTE} residSmaller (lteSuccRight $ lteSuccRight $ lteSuccRight $ reflexive {rel=LTE}))))
  parseType context (TForSome :: TVar l :: TDot :: xs) (Access acc) = do (ty, (Element resid residSmaller)) <- parseType (addTypeBinding context l) xs (acc xs (lteSuccRight $ lteSuccRight $ reflexive {rel=LTE}))
                                                                         pure (TySome ty, (Element resid (transitive {rel=LTE} residSmaller (lteSuccRight $ lteSuccRight $ lteSuccRight $ reflexive {rel=LTE}))))
  parseType context tokens (Access acc) = do (ty, (Element resid residSmaller)) <- parsePartType context tokens (Access acc)
                                             case resid of
                                                  (TArrow :: xs) => do (tyRight, (Element resid' residSmaller')) <- parseType context xs (acc xs (lteSuccLeft residSmaller))
                                                                       pure (TyArr ty tyRight, (Element resid' (transitive {rel=LTE} residSmaller' (lteSuccLeft $ lteSuccLeft residSmaller))))
                                                  xs => Right (ty, (Element xs residSmaller))

ParseResult : Nat -> Nat -> List Token -> Type
ParseResult n m tokens = (Term n m, (Subset (List Token) (\resid => resid `Smaller` tokens)))

mutual
  --Parse right hand sides of type or term apllication
  parseTyTerms : {n, m : Nat} -> (context : Context n m) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (List (Ty m), List (Term n m), (Subset (List Token) (\resid => resid `Smaller` tokens)))
  parseTyTerms context (TLSquareBrace :: xs) (Access acc) = do (type, Element (TRSquareBrace :: resid) residSmaller) <- parseType context xs (acc xs (reflexive {rel=LTE}))
                                                               | _ => Left "Expected ']'"
                                                               (types, terms, Element resid' residSmaller') <- parseTyTerms context resid (acc resid (lteSuccLeft $ lteSuccRight residSmaller))
                                                               pure (type :: types, terms, Element resid' (transitive {rel=LTE} residSmaller' (lteSuccLeft $ lteSuccLeft $ lteSuccRight residSmaller)))
  parseTyTerms context tokens acc = do (terms, resid) <- parseTerms context tokens acc
                                       pure ([], forget terms, resid)

  --get nonempty list of terms for term application
  parseTerms : {n, m : Nat} -> (context : Context n m) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (List1 (Term n m), (Subset (List Token) (\resid => resid `Smaller` tokens)))
  parseTerms context tokens (Access acc) = do (term, (Element resid residSmaller)) <- parseTerm context tokens (Access acc)
                                              case parseTyTerms context resid (acc resid residSmaller) of
                                                   (Left _) => Right (term ::: [], (Element resid residSmaller))
                                                   (Right (types, terms, (Element resid' residSmaller'))) => Right (foldl TmTApp term types ::: terms, (Element resid' (transitive {rel=LTE} residSmaller' (lteSuccLeft residSmaller))))

  --get all terms and apply them
  parseWhole : {n, m : Nat} -> (context : Context n m) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (ParseResult n m tokens)
  parseWhole context tokens acc = do (terms, resid) <- parseTerms context tokens acc
                                     Right (foldl1 TmApp terms, resid)

  --parse a term without an application
  parseTerm : {n, m : Nat} -> (context : Context n m) -> (tokens : List Token) -> (0 acc : SizeAccessible tokens) -> Either String (ParseResult n m tokens)
  parseTerm context (TLParen :: xs) (Access acc) = do (term, Element (TRParen :: resid) residSmaller) <- parseWhole context xs (acc xs (reflexive {rel=LTE}))
                                                      | _ => Left "Expected ')'"
                                                      pure (term, Element resid (lteSuccLeft $ lteSuccRight residSmaller))
  parseTerm context ((TVar name) :: xs) (Access acc) = case getTermIndex context name of
                                                            Nothing => Left (name ++ " is not bound")
                                                            (Just idx) => Right (TmVar idx, (Element xs (reflexive {rel = LTE})))
  parseTerm context (TLambda :: (TVar name) :: TColon :: xs) (Access acc) = do (type, (Element (TDot :: ys) residSmaller)) <- parseType context xs (acc xs (lteSuccRight $ lteSuccRight $ (reflexive {rel = LTE})))
                                                                                | _ => Left "Expected '.'"
                                                                               (body, (Element resid residSmaller')) <- parseWhole (addTermBinding context name type) ys (acc ys (lteSuccLeft $ lteSuccRight $ lteSuccRight $ lteSuccRight residSmaller))
                                                                               pure (TmAbs type body, (Element resid (transitive {rel=LTE} residSmaller' (lteSuccLeft $ lteSuccLeft $ lteSuccRight $ lteSuccRight $ lteSuccRight residSmaller))))
  parseTerm context (TLambda :: (TVar name) :: TDot :: xs) (Access acc) = do (body, (Element resid residSmaller)) <- parseWhole (addTypeBinding context name) xs (acc xs (lteSuccRight $ lteSuccRight $ reflexive {rel=LTE}))
                                                                             pure (TmTAbs body, (Element resid (lteSuccRight $ lteSuccRight $ lteSuccRight residSmaller)))
  parseTerm context (TLBrace :: TStar :: xs) (Access acc) = do (indType, Element (TComma :: ys) residSmaller) <- parseType context xs (acc xs (lteSuccRight $ reflexive {rel=LTE}))
                                                               | _ => Left "Expected ','"
                                                               (body, Element (TRBrace :: TAs :: zs) residSmaller') <- parseWhole context ys (acc ys (lteSuccLeft $ lteSuccRight $ lteSuccRight residSmaller))
                                                               | _ => Left "Expected '} as'"
                                                               (packType, Element resid residSmaller'') <- parseType context zs (acc zs (lteSuccLeft $ lteSuccLeft $ transitive {rel=LTE} residSmaller' $ lteSuccLeft $ lteSuccLeft $ lteSuccRight $ lteSuccRight residSmaller))
                                                               pure (TmPack indType body packType, Element resid (transitive {rel=LTE} residSmaller'' $ lteSuccLeft $ lteSuccLeft $ lteSuccLeft $ transitive {rel=LTE} residSmaller' $ lteSuccLeft $ lteSuccLeft $ lteSuccRight $ lteSuccRight residSmaller))
  parseTerm context (TLet :: TLBrace :: (TVar tyName) :: TComma :: (TVar tmName) :: TRBrace :: TEqual :: xs) (Access acc) =
    do (packTerm, Element (TIn :: ys) residSmaller) <- parseWhole context xs (acc xs (lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ reflexive {rel=LTE}))
       | _ => Left "Expected 'in'"
       (body, Element resid residSmaller') <- parseWhole (addTermBinding (addTypeBinding context tyName) tmName (TyVar FZ)) ys --the type of the variable binding is a lie. We will get a correct type when we do typechecking
                                                         (acc ys (lteSuccLeft $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ residSmaller))
       pure (TmUnpack packTerm body, Element resid (transitive {rel=LTE} residSmaller' $ lteSuccLeft $ lteSuccLeft $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight $ lteSuccRight residSmaller))
  parseTerm _ _ _ = Left "Invalid Term"

export
parse : String -> Either String (Term 0 0)
parse str = do
  tokens <- tokenize str
  (term, (Element [] _)) <- parseWhole emptyContext tokens (sizeAccessible tokens)
    | _ => Left "Extra tokens at end of term"
  pure term
