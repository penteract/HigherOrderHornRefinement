{-

-}
module HRSParser where

import HOCHC.Tokeniser
import HOCHC.Parser
import HOCHC.DataTypes
import HOCHC.TypeCheck

import Text.Parsec.Prim
import Text.Parsec.Combinator

import Data.Char
import Data.Maybe
import Data.List(sortBy,union,nub,intercalate)
import Data.Ord(comparing)
import Control.Applicative((<**>))


import System.IO.Unsafe

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


ruleLine :: MyParser HorsRule
ruleLine = do
    (fn:args) <- many1 identifier
    tok "->"
    body <- formula
    tok "."
    return (fn,args,body)

tr :: MyParser ((AState,Constant),[AState])
tr = do
    q <- identifier
    --tok ","
    c <- identifier
    tok "->"
    qs <- many identifier
    tok "."
    return ((q,c), qs)

section :: String -> MyParser a -> MyParser a
section s p = do
    tok "%" >> tok ("BEGIN"++s)
    r <- p
    tok "%" >> tok ("END"++s)
    return r

file :: MyParser HOMCP
file = do
    rules <- section "G" $ many1 ruleLine
    let nonterminals = map (\(x,_,_)->x) rules
    let terminals = []
    trans <- section "A" $ many1 tr
    let trfn = curry $ (flip lookup) trans
    let qs = nub [q | ((q,_),_) <-trans]
    seq (unsafePerformIO $print$ typeCheck rules ) (return ((terminals,[],rules),trfn,qs))

horssymbols = map return ":;,{}()=%." ++["->"]


parseFile :: String -> String -> Either String HOMCP
parseFile fname contents = fromParse (do
    ts <- tokeniseFromFile (horssymbols) fname contents
    let body =  [ t | t@(_,tty,_) <- ts, tty/=NewLine]
    runParser file () fname body)

fromParse (Left x) = Left $ show x
fromParse (Right x) =  Right x

--for testing
qp =  (>>= (runParser formula () "" . map cannonise)) . tokeniseFromOps  (symbols ++ map fst cannonicals)
