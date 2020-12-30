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

oneStepMaybeSmaller : (tIn : Term) -> Maybe (tOut : Term ** tOut `Smaller` tIn)
oneStepMaybeSmaller (TmIf TmTrue t e) = Just (t ** LTESucc (lteSuccRight (lteAddRight (size t))))
oneStepMaybeSmaller (TmIf TmFalse t e) = Just (e ** LTESucc (lteSuccRight (rewrite plusZeroLeftNeutral (size t) in rewrite plusCommutative (size t) (size e) in lteAddRight (size e))))
oneStepMaybeSmaller (TmIf g t e) = do (newGuard ** prfSmaller) <- oneStepMaybeSmaller g
                                      pure (TmIf newGuard t e ** LTESucc (plusLteMonotoneRight (size e) (S (size newGuard + size t)) (size g + size t) (plusLteMonotoneRight (size t) (S (size newGuard)) (size g) prfSmaller)))
oneStepMaybeSmaller (TmSucc x) with (isNumeric x)
  oneStepMaybeSmaller (TmSucc _) | (Yes _) = Nothing
  oneStepMaybeSmaller (TmSucc x) | (No _) = do (newX ** prfSmaller) <- oneStepMaybeSmaller x
                                               pure (TmSucc newX ** LTESucc prfSmaller)
oneStepMaybeSmaller (TmPred x) with (isNumeric x)
  oneStepMaybeSmaller (TmPred TmZero) | (Yes ZeroIsNumeric) = Just (TmZero ** lteRefl)
  oneStepMaybeSmaller (TmPred (TmSucc n)) | (Yes (SuccIsNumeric _)) = Just (n ** lteSuccRight lteRefl)
  oneStepMaybeSmaller (TmPred x) | (No _) = do (newX ** prfSmaller) <- oneStepMaybeSmaller x
                                               pure (TmPred newX ** LTESucc prfSmaller)
oneStepMaybeSmaller (TmIszero x) with (isNumeric x)
  oneStepMaybeSmaller (TmIszero TmZero) | (Yes ZeroIsNumeric) = Just (TmTrue ** lteRefl)
  oneStepMaybeSmaller (TmIszero (TmSucc _)) | (Yes (SuccIsNumeric _)) = Just (TmFalse ** LTESucc (LTESucc LTEZero))
  oneStepMaybeSmaller (TmIszero x) | (No _) = do (newX ** prfSmaller) <- oneStepMaybeSmaller x
                                                 pure (TmIszero newX ** LTESucc prfSmaller)
oneStepMaybeSmaller _ = Nothing

export
eval : Term -> Term
eval x = sizeRec step x
  where
    step : (x : Term) -> ((y : Term) -> LTE (S (size y)) (size x) -> Term) -> Term
    step x f = case oneStepMaybeSmaller x of
                    Nothing => x
                    (Just (y ** ySmallerX)) => f y ySmallerX

--covering
--eval : Term -> Term
--eval term = case oneStep term of
--              Nothing => term
--              (Just term') => eval term'
