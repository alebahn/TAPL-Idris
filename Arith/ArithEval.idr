module ArithEval

import Control.WellFounded
import Data.Nat

import ArithParser

%default total

data IsNumeric : Term -> Type where
  ZeroIsNumeric : IsNumeric TmZero
  SuccIsNumeric : IsNumeric n -> IsNumeric (TmSucc n)

Uninhabited (IsNumeric TmTrue) where
  uninhabited ZeroIsNumeric impossible
  uninhabited (SuccIsNumeric x) impossible

Uninhabited (IsNumeric TmFalse) where
  uninhabited ZeroIsNumeric impossible
  uninhabited (SuccIsNumeric x) impossible

Uninhabited (IsNumeric (TmIf g t f)) where
  uninhabited ZeroIsNumeric impossible
  uninhabited (SuccIsNumeric x) impossible

Uninhabited (IsNumeric (TmPred x)) where
  uninhabited ZeroIsNumeric impossible
  uninhabited (SuccIsNumeric x) impossible

Uninhabited (IsNumeric (TmIszero x)) where
  uninhabited ZeroIsNumeric impossible
  uninhabited (SuccIsNumeric x) impossible

isNumeric : (t : Term) -> Dec (IsNumeric t)
isNumeric TmTrue = No uninhabited
isNumeric TmFalse = No uninhabited
isNumeric (TmIf g t f) = No uninhabited
isNumeric TmZero = Yes ZeroIsNumeric
isNumeric (TmSucc x) = case isNumeric x of
                            (Yes prf) => Yes (SuccIsNumeric prf)
                            (No contra) => No (\(SuccIsNumeric x) => contra x)
isNumeric (TmPred x) = No uninhabited
isNumeric (TmIszero x) = No uninhabited

Sized Term where
  size TmTrue = 1
  size TmFalse = 1
  size (TmIf g t e) = S (size g + size t + size e)
  size TmZero = 1
  size (TmSucc x) = S (size x)
  size (TmPred x) = S (size x)
  size (TmIszero x) = S (size x)

oneStep : (tIn : Term) -> Maybe (tOut : Term ** tOut `Smaller` tIn)
oneStep (TmIf TmTrue t e) = Just (t ** LTESucc (lteSuccRight (lteAddRight (size t))))
oneStep (TmIf TmFalse t e) = Just (e ** LTESucc (lteSuccRight (rewrite plusZeroLeftNeutral (size t) in rewrite plusCommutative (size t) (size e) in lteAddRight (size e))))
oneStep (TmIf g t e) = do (newGuard ** prfSmaller) <- oneStep g
                          pure (TmIf newGuard t e ** LTESucc (plusLteMonotoneRight (size e) (S (size newGuard + size t)) (size g + size t) (plusLteMonotoneRight (size t) (S (size newGuard)) (size g) prfSmaller)))
oneStep (TmSucc x) with (isNumeric x)
  oneStep (TmSucc _) | (Yes _) = Nothing
  oneStep (TmSucc x) | (No _) = do (newX ** prfSmaller) <- oneStep x
                                   pure (TmSucc newX ** LTESucc prfSmaller)
oneStep (TmPred x) with (isNumeric x)
  oneStep (TmPred TmZero) | (Yes ZeroIsNumeric) = Just (TmZero ** (reflexive {rel=LTE}))
  oneStep (TmPred (TmSucc n)) | (Yes (SuccIsNumeric _)) = Just (n ** lteSuccRight (reflexive {rel=LTE}))
  oneStep (TmPred x) | (No _) = do (newX ** prfSmaller) <- oneStep x
                                   pure (TmPred newX ** LTESucc prfSmaller)
oneStep (TmIszero x) with (isNumeric x)
  oneStep (TmIszero TmZero) | (Yes ZeroIsNumeric) = Just (TmTrue ** (reflexive {rel=LTE}))
  oneStep (TmIszero (TmSucc _)) | (Yes (SuccIsNumeric _)) = Just (TmFalse ** LTESucc (LTESucc LTEZero))
  oneStep (TmIszero x) | (No _) = do (newX ** prfSmaller) <- oneStep x
                                     pure (TmIszero newX ** LTESucc prfSmaller)
oneStep _ = Nothing

export
eval : Term -> Term
eval x = sizeRec step x
  where
    step : (x : Term) -> ((y : Term) -> LTE (S (size y)) (size x) -> Term) -> Term
    step x f = case oneStep x of
                    Nothing => x
                    (Just (y ** ySmallerX)) => f y ySmallerX

data IsValue : Term -> Type where
  TrueIsValue : IsValue TmTrue
  FalseIsValue : IsValue TmFalse
  NumIsValue : IsNumeric tm -> IsValue tm

Uninhabited (IsValue (TmIf g t e)) where
  uninhabited (NumIsValue ifIsNum) = uninhabited ifIsNum

Uninhabited (IsValue (TmPred x)) where
  uninhabited (NumIsValue predIsNum) = uninhabited predIsNum

Uninhabited (IsValue (TmIszero x)) where
  uninhabited (NumIsValue iszeroIsNum) = uninhabited iszeroIsNum

isValue : (t : Term) -> Dec (IsValue t)
isValue TmTrue = Yes TrueIsValue
isValue TmFalse = Yes FalseIsValue
isValue (TmIf g t e) = No uninhabited
isValue TmZero = Yes (NumIsValue ZeroIsNumeric)
isValue (TmSucc x) = case isNumeric x of
                          (Yes prf) => Yes (NumIsValue (SuccIsNumeric prf))
                          (No contra) => No (\(NumIsValue (SuccIsNumeric prf)) => contra prf)
isValue (TmPred x) = No uninhabited
isValue (TmIszero x) = No uninhabited

export
bigStepEval : Term -> Maybe Term
bigStepEval t with (isValue t)
  bigStepEval t | (Yes prf) = Just t
  bigStepEval TmTrue | (No contra) = void $ contra TrueIsValue
  bigStepEval TmFalse | (No contra) = void $ contra FalseIsValue
  bigStepEval TmZero | (No contra) = void $ contra (NumIsValue ZeroIsNumeric)
  bigStepEval (TmIf g t e) | (No _) = case bigStepEval g of
                                           (Just TmTrue) => bigStepEval t
                                           (Just TmFalse) => bigStepEval e
                                           _ => Nothing
  bigStepEval (TmSucc x) | (No _) = do xNext <- bigStepEval x
                                       case isNumeric xNext of
                                            (Yes _) => pure (TmSucc xNext)
                                            (No _) => Nothing
  bigStepEval (TmPred x) | (No _) = do xNext <- bigStepEval x
                                       case xNext of
                                            TmZero => pure TmZero
                                            TmSucc num => pure num
                                            _ => Nothing
  bigStepEval (TmIszero x) | (No _) = do xNext <- bigStepEval x
                                         case xNext of
                                              TmZero => pure TmTrue
                                              TmSucc num => pure TmFalse
                                              _ => Nothing
