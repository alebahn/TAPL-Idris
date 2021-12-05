module Tokens

import Data.Fin
import Data.String
import Data.List1
import Data.List

%default total

public export
data Token = TLambda
           | TVar String
           | TDot
           | TLParen
           | TRParen
           | TColon
           | TBool
           | TArrow
           | TTrue
           | TFalse
           | TIf
           | TThen
           | TElse

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
stringToToken ":" = Right TColon
stringToToken "Bool" = Right TBool
stringToToken "->" = Right TArrow
stringToToken "true" = Right TTrue
stringToToken "false" = Right TFalse
stringToToken "if" = Right TIf
stringToToken "then" = Right TThen
stringToToken "else" = Right TElse
stringToToken str = if isValidVarName str
                       then Right (TVar str)
                       else Left ("Invalid Token: " ++ str)

partitionStringListChar : Char -> List String -> List String
partitionStringListChar c strs = concat $ map (\subs => intersperse (cast c) (forget $ split (== c) subs)) strs

startsWithStringOrJoin : (chrPrefix : Char) -> (strPrefix : String) -> (head : String) -> (rest : List String) -> List1 String
startsWithStringOrJoin c strPrefix head [] = head ::: []
startsWithStringOrJoin c strPrefix head (str :: strs) = if isPrefixOf strPrefix str
                                                           then let subs = substr (length strPrefix) (length str) str in
                                                                    head ::: (forget $ startsWithStringOrJoin c strPrefix subs strs)
                                                           else let joined = head ++ (strCons c str) in
                                                                    startsWithStringOrJoin c strPrefix joined strs

partitionStringWithString : (splitter : String) -> (whole : String) -> List String
partitionStringWithString splitter whole = case strUncons splitter of
                                                Nothing => [whole]
                                                (Just (c, cs)) => let (first ::: rest) = split (== c) whole in
                                                                      intersperse splitter (forget $ startsWithStringOrJoin c cs first rest)

partitionStringListString : String -> List String -> List String
partitionStringListString str strs = concat $ map (partitionStringWithString str) strs

export
tokenize : String -> Either String (List Token)
tokenize s = let spaceSplit = forget $ split isSpace s
                 arrowSplit = partitionStringListString "->" spaceSplit
                 dotSplit = partitionStringListChar '.' arrowSplit
                 lParenSplit = partitionStringListChar '(' dotSplit
                 rParenSplit = partitionStringListChar ')' lParenSplit
                 backSlashSplit = partitionStringListChar '\\' rParenSplit
                 colonSplit = partitionStringListChar ':' backSlashSplit
                 removeBlank = filter (/="") colonSplit in
                 traverse stringToToken removeBlank
