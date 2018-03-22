{-

-}
module HCParser where

import HOCHC.Parser
import HOCHC.Tokeniser

import Text.Parsec.Prim
import Text.Parsec.Combinator

import Data.Char
import Data.Maybe
import Data.List(sortBy)
import Data.Ord(comparing)
import HOCHC.DataTypes
import Control.Applicative((<**>))

lineParser :: MyParser [Term]
lineParser = (formula >>= return.return)
         <|> parserReturn []

parser :: MyParser [Term]
parser = do res <- chainl lineParser (tok "\n" >> return (++)) []
            eof
            return res



environmentLine :: MyParser DeltaEnv
environmentLine = (do
      (Variable v) <- variable
      tok ":"
      s<-sort
      return [(v,s)])
    <|> return []

separator = (tok ";" >> tok "\n") <|> tok "\n" <|> return ""



file :: MyParser (DeltaEnv,[Term],Term)
file = do
    tok "environment" >> tok "\n"
    d <- chainl1 environmentLine (tok "\n">>return (++))
    separator >> tok "program" >> tok "\n"
    prog <- chainl1 lineParser (tok "\n" >> return (++))
    separator >> tok "goal" >> tok "\n"
    goal <- formula
    eof <|> (tok ";" >> eof)
    return (d,prog,goal)


parseFile :: String -> String -> Either String (DeltaEnv,[Term],Term)
parseFile fname contents = fromParse (do
    ts <- tokeniseFromFile (["environment","program","goal"] ++ symbols ++ map fst cannonicals) fname contents
    let body = map cannonise ts
    runParser file () fname body)

fromParse (Left x) = Left $ show x
fromParse (Right x) =  Right x

--for testing
--qp =  (>>= (runParser formula () "" . map cannonise)) . tokeniseFromOps  (symbols ++ map fst cannonicals)
