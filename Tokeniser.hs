{-
Functions for turning input text into a list of tokens.
These accept a list of constants to recognise.
Newlines followed by whitespace are ignored
    (so you can have multiline definitions if later lines start with whitespace)
Comments begin with #, the remainder of the line is ignored
-}

module Tokeniser(
    tokeniseFromOps,tokeniseFromFile,
    Token,
    TokenType(Operator, Identifier, Number, NewLine)
    ) where

import Data.Char

import Text.Parsec.Pos
import Text.Parsec.Error
import Data.List (partition,find,elemIndices)
import Control.Applicative ((<|>))
import Data.Maybe (fromJust,isJust)
import Data.Bifunctor


type Token = (String,TokenType,SourcePos)
data TokenType = Operator | Identifier | Number | NewLine deriving (Show,Eq)


splitByStart :: [String] -> [(Char,[String])]
splitByStart [] = []
splitByStart ((c:a):ss) = (c,a:map tail startWithc):splitByStart rest
            where (startWithc,rest) = partition ((==c).head) ss
splitByStart _ = error "does not expect the empty string"

-- A search tree for constants
-- This is slightly overkill - there enough constants to warrant it.
data Tree = Tree [(Char,Tree)] (Maybe String) deriving Show

-- Construct a Tree from a list of constants for faster lookups
makeTree :: [String] -> Tree
makeTree = make' ""
    where make' cur rest = let (node,longer) = partition (=="") rest in
             Tree (map (\ (c,xs)-> (c, make' (c:cur) xs)) (splitByStart longer))
                  (if null node then Nothing else Just (reverse cur))

-- Get the longest match
getFromTree :: Tree -> String -> Maybe (String,String)
getFromTree (Tree ts mx) "" = mx>>=(\x->Just (x,""))
getFromTree (Tree ts mx) s = (lookup (head s) ts >>= (\t -> getFromTree t (tail s)))
            <|> (mx >>= (\x->Just (x,s)))


-- The remainder of a piece of text.
type Remainder = (String,SourcePos)

-- get a single token in a form suitable for tokengetters
getq :: TokenType -> (String -> (String,String)) -> (Remainder -> ([Token],Remainder))
getq typ f (ss,p) = ([(t,typ,p)] ,(rest, incSourceColumn p c))
        where
            (t,rest) = f ss
            c = length t

-- A list of functions to be applied in order and detect the next token in a stream
type Tgtrs = [(String -> Bool, Remainder -> ([Token],Remainder))]

tokengetters :: Tree -> [(String -> Bool, Remainder -> ([Token],Remainder))]
tokengetters t = [
            ((== '\n').head, getNL.first tail),
            (isSpace.head, \(ss,p) -> ([],(tail ss,incSourceColumn p 1))),
            (isJust . getFromTree t, getq Operator (fromJust . getFromTree t)),
            (isDigit.head, getq Number (span isDigit)),
            (isAlpha.head, getq Identifier (span (\x->isAlphaNum x || x=='_')) )
            ]
            where getNL (ss,p) = (if ss=="" || isSpace (head ss) || head ss == '#'
                   then []
                   else [("\n",NewLine,p)]
                   ,( ss, incSourceLine (setSourceColumn p 0) 1))


tokeniseFromOps :: [String] -> String -> Either ParseError [Token]
tokeniseFromOps ops' = tokeniseFromFile ops' "source"


tokeniseFromFile :: [String] -> String -> String -> Either ParseError [Token]
tokeniseFromFile ops' fname s = let (kwds,ops) = partition (all isAlpha) ops' in
    map (\(i,t,p)-> (i,(if i `elem` kwds then Operator else t),p)) <$>
      (tokeniseFromGetters $ tokengetters $ makeTree ops)  (s,initialPos fname)


tokeniseFromGetters :: Tgtrs -> Remainder -> Either ParseError [Token]
tokeniseFromGetters gs ("",_) = Right []
tokeniseFromGetters gs ('#':s,f) = tokeniseFromGetters gs (dropWhile (/= '\n') s,f)
tokeniseFromGetters gs s = case find (\(x,_) -> x $ fst s) gs of
            Nothing -> Left (newErrorMessage (Message "error in tokeniser ") (snd s))
            Just (_,f) -> let (a,rest) = f s in (
                            tokeniseFromGetters gs rest >>= Right . (a++))
