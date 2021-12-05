module ArithTokens

import Data.Fin
import Data.String
import Data.List1

%default total

public export
data Token = TTrue
           | TFalse
           | TIf
           | TThen
           | TElse
           | TZero
           | TSucc
           | TPred
           | TIszero

stringToToken : String -> Either String Token
stringToToken "true" = Right TTrue
stringToToken "false" = Right TFalse
stringToToken "if" = Right TIf
stringToToken "then" = Right TThen
stringToToken "else" = Right TElse
stringToToken "0" = Right TZero
stringToToken "succ" = Right TSucc
stringToToken "pred" = Right TPred
stringToToken "iszero" = Right TIszero
stringToToken badToken = Left ("Invalid Token: " ++ badToken)

export
tokenize : String -> Either String (List Token)
tokenize xs = let splitStrings = forget $ split (==' ') xs in
                  traverse stringToToken splitStrings
