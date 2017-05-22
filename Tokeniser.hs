{-
Functions for turning input text into a list of tokens.
This module does not fix the syntax used, but accepts a list of constants to recognise.
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
                  (if node==[] then Nothing else Just (reverse cur))
               
-- Get the longest match
getFromTree :: Tree -> String -> Maybe (String,String)
getFromTree (Tree ts mx) "" = mx>>=(\x->Just (x,""))
getFromTree (Tree ts mx) s = (lookup (head s) ts >>= (\t -> getFromTree t (tail s))) 
            <|> (mx >>= (\x->Just (x,s)))


-- The remainder of a piece of text.
type Remainder = (String,SourcePos)
            
getq :: TokenType -> (String -> (String,String)) -> (Remainder -> ([Token],Remainder))
getq typ f (ss,p) = ([(t,typ,p)] , 
                 (rest, incSourceLine (if n==0 then incSourceColumn p c else setSourceColumn p (c+1)) n ))
        where
            (t,rest) = f ss 
            n = length $ elemIndices '\n' t
            c = length $ takeWhile (/='\n') $ reverse t

-- A list of functions to be applied in order and detect the next token in a stream
type Tgtrs = [(String -> Bool, Remainder -> ([Token],Remainder))]

tokengetters :: Tree -> [(String -> Bool, Remainder -> ([Token],Remainder))]
tokengetters t = [
            ((== '\n').head, getq NewLine $ \ss -> ("\n",tail ss)),
            (isSpace.head, \(ss,p) -> ([],(tail ss,incSourceColumn p 1))),
            (isJust.(getFromTree t), getq Operator (fromJust.(getFromTree t))),
            (isDigit.head, getq Number (break (not.isDigit))),
            (isAlpha.head, getq Identifier (break (\x->not (isAlphaNum x || x=='_'))))
            ]


tokeniseFromOps :: [String] -> String -> Either ParseError [Token]
tokeniseFromOps ops' s = (tokeniseFromGetters $ tokengetters $ makeTree ops')  (s,initialPos "source")


tokeniseFromFile :: [String] -> String -> String -> Either ParseError [Token]
tokeniseFromFile ops' fname s = (tokeniseFromGetters $ tokengetters $ makeTree ops')  (s,initialPos fname)


tokeniseFromGetters :: Tgtrs -> Remainder -> Either ParseError [Token]
tokeniseFromGetters gs ("",_) = Right []
tokeniseFromGetters gs ('#':s,f) = tokeniseFromGetters gs (dropWhile (/= '\n') s,f)
tokeniseFromGetters gs s = case find (\(x,_) -> x $ fst s) gs of
            Nothing -> Left (newErrorMessage (Message "error in tokeniser ") (snd s))
            Just (_,f) -> let (a,rest)=(f s) in (tokeniseFromGetters gs rest >>= Right . (a++))
            
        
