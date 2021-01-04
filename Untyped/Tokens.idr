module Tokens

import Data.Fin
import Data.Strings
import Data.List1
import Data.List

%default total

public export
data Token = TLambda
           | TVar String
           | TDot
           | TLParen
           | TRParen

isValidVarChar : Char -> Bool
isValidVarChar '\'' = True
isValidVarChar '-' = True
isValidVarChar x = isAlpha x

isValidVarName : String -> Bool
isValidVarName str = all isValidVarChar (unpack str)

stringToToken : String -> Either String Token
stringToToken "lambda" = Right TLambda
stringToToken "." = Right TDot
stringToToken "(" = Right TLParen
stringToToken ")" = Right TRParen
stringToToken "\\" = Right TLambda
stringToToken str = if isValidVarName str
                       then Right (TVar str)
                       else Left ("Invalid Token: " ++ str)

partitionStringList : Char -> List String -> List String
partitionStringList c strs = concat $ map (\subs => intersperse (cast c) (forget $ split (== c) subs)) strs

export
tokenize : String -> Either String (List Token)
tokenize s = let spaceSplit = forget $ split (== ' ') s
                 dotSplit = partitionStringList '.' spaceSplit
                 lParenSplit = partitionStringList '(' dotSplit
                 rParenSplit = partitionStringList ')' lParenSplit
                 backSlashSplit = partitionStringList '\\' rParenSplit
                 removeBlank = filter (/="") backSlashSplit in
                 traverse stringToToken removeBlank
