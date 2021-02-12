module Tokens

import Data.Fin
import Data.Strings
import Data.List1
import Data.List
import Control.WellFounded
import Data.Nat

%default total

public export
data Token = TLambda
           | TVar String
           | TDot
           | TLParen
           | TRParen
           | TColon
           | TArrow
           | TLBrace
           | TRBrace
           | TEqual
           | TComma
           | TTop
           | TBot

isValidVarChar : Char -> Bool
isValidVarChar '\'' = True
isValidVarChar '-' = True
isValidVarChar x = isAlpha x

isValidVarName : String -> Bool
isValidVarName str = all isValidVarChar (unpack str)

stringToToken : String -> Either String Token
stringToToken "lambda" = Right TLambda
stringToToken "Top" = Right TTop
stringToToken "Bot" = Right TBot
stringToToken "." = Right TDot
stringToToken "(" = Right TLParen
stringToToken ")" = Right TRParen
stringToToken "\\" = Right TLambda
stringToToken ":" = Right TColon
stringToToken "->" = Right TArrow
stringToToken "{" = Right TLBrace
stringToToken "}" = Right TRBrace
stringToToken "=" = Right TEqual
stringToToken "," = Right TComma
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

singleCharTokens : List Char
singleCharTokens = unpack ".()\\:{}=,"

packBufferCons : (buffer : List Char) -> (tail : List String) -> List String
packBufferCons [] tail = tail
packBufferCons buffer tail = pack buffer :: tail

partitionAll : List Char -> List Char -> List String
partitionAll ('-' :: '>' :: xs) buffer = packBufferCons buffer ("->" :: partitionAll xs [])
partitionAll (x :: xs) buffer = if isSpace x 
                                   then packBufferCons buffer (partitionAll xs [])
                                   else if elem x singleCharTokens 
                                           then packBufferCons buffer (singleton x :: partitionAll xs [])
                                           else partitionAll xs (buffer ++ [x])
partitionAll [] buffer = packBufferCons buffer []

export
tokenize : String -> Either String (List Token)
tokenize s = let partitioned = partitionAll (unpack s) [] in
                 traverse stringToToken partitioned
