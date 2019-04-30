{-

-}
module RSParser where

import HOCHC.Tokeniser
import HOCHC.Parser

import Text.Parsec.Prim
import Text.Parsec.Combinator

import Data.Char
import Data.Maybe
import Data.List(sortBy,union,nub,intercalate)
import Data.Ord(comparing)
import HOCHC.DataTypes
import Control.Applicative((<**>))

type Terminals = [(Constant, Sort)]
type Nonterminals = [(Variable, Sort)]
type HorsRule = (Variable, [Variable], Term) --Restricted term only
type HORS = (Terminals,Nonterminals,[HorsRule])

type AState = String

type Automaton = AState -> Constant -> Maybe [AState]

type HOMCP = (HORS,Automaton,[AState])

printa :: HOMCP -> String
printa ((ts,nts,rs),d,qs) =unlines [
    "terminals {",
    ts >>= (\(c,s) -> c++":"++prnS s++";\n"),
    "}","nonterminals {",
    nts >>= (\(c,s) -> c++":"++prnS s++";\n"),
    "}","rules {",
    rs >>= (\(v,args,t) -> intercalate " " (v:args)++"=" ++prnt t ++";\n"),
    "}",
    unlines [q++","++t++"->"++show (d q t) | q <- qs , (t,_) <- ts]
    ]


--otoi Bool = Int
--otoi (Arrow a b) = Arrow (otoi a) (otoi b)


horsunit = tok "o" >> return Int

horsType :: MyParser Sort
horsType = chainr1 (horsunit <|> parens horsType)
                (tok "->" >> return Arrow)


typeLine :: MyParser (String,Sort)
typeLine = do
      v <- identifier
      tok ":"
      s<-horsType
      tok ";"
      return (v,s)
ruleLine :: MyParser HorsRule
ruleLine = do
    (fn:args) <- many1 identifier
    tok "="
    body <- formula
    tok ";"
    return (fn,args,body)

tr :: MyParser ((AState,Constant),[AState])
tr = do
    q <- identifier
    tok ","
    c <- identifier
    tok "->"
    qs <- many identifier
    tok ";"
    return ((q,c), qs)

section :: String -> MyParser a -> MyParser a
section s p = do
    tok s >> tok "{"
    r <- p
    tok "}"
    return r

file :: MyParser HOMCP
file = do
    terminals <- section "terminals" $ many1 typeLine
    nonterminals <-section "nonterminals" $ many1 typeLine
    rules <- section "rules" $ many1 ruleLine

    trans <- section "transitions" $ many1 tr
    let trfn = curry $ (flip lookup) trans
    let qs = nub [q | ((q,_),_) <-trans]
    return ((terminals,nonterminals,rules),trfn,qs)

horssymbols = map return ":;,{}()=" ++["->"]


parseFile :: String -> String -> Either String HOMCP
parseFile fname contents = fromParse (do
    ts <- tokeniseFromFile (horssymbols) fname contents
    let body =  [ t | t@(_,tty,_) <- ts, tty/=NewLine]
    runParser file () fname body)

fromParse (Left x) = Left $ show x
fromParse (Right x) =  Right x

--for testing
qp =  (>>= (runParser formula () "" . map cannonise)) . tokeniseFromOps  (symbols ++ map fst cannonicals)
