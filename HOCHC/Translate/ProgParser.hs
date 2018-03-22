{-

-}
module ProgParser where

import HOCHC.Tokeniser
import HOCHC.Parser

import Text.Parsec.Prim
import Text.Parsec.Combinator

import Data.Char
import Data.Maybe
import Data.List(sortBy,union)
import Data.Ord(comparing)
import HOCHC.DataTypes
import Control.Applicative((<**>))


lineParser :: MyParser Definition
lineParser = do
    do
        optionMaybe$ tok "let"
        optionMaybe$ tok "rec"
    (fn:args) <- many1 identifier
    oneOf [":=","="]
    body <- formula
    return (fn,args,body)

file :: MyParser [Definition]
file = do res <- chainr ((:[])<$>lineParser) (tok "\n" >> return (++)) []
          eof
          return res

parseFile :: String -> String -> Either String [Definition]
parseFile fname contents = fromParse (do
    ts <- tokeniseFromFile (["assert"] ++symbols ++ map fst cannonicals) fname contents
    let body = map cannonise ts
    runParser file () fname body)

fromParse (Left x) = Left $ show x
fromParse (Right x) =  Right x

--for testing
qp =  (>>= (runParser formula () "" . map cannonise)) . tokeniseFromOps  (symbols ++ map fst cannonicals)
