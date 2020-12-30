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
  oneStep (TmPred TmZero) | (Yes ZeroIsNumeric) = Just (TmZero ** lteRefl)
  oneStep (TmPred (TmSucc n)) | (Yes (SuccIsNumeric _)) = Just (n ** lteSuccRight lteRefl)
  oneStep (TmPred x) | (No _) = do (newX ** prfSmaller) <- oneStep x
                                   pure (TmPred newX ** LTESucc prfSmaller)
oneStep (TmIszero x) with (isNumeric x)
  oneStep (TmIszero TmZero) | (Yes ZeroIsNumeric) = Just (TmTrue ** lteRefl)
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

--covering
--eval : Term -> Term
--eval term = case oneStep term of
--              Nothing => term
--              (Just term') => eval term'
