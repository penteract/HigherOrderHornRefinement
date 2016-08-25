module Tokeniser(
    tokeniseFromOps,tokeniseFromFile,
    Token,
    TokenType(Operator, Identifier, Number, NewLine)
    ) where

import Data.Char
import Text.ParserCombinators.Parsec(SourcePos)
import Text.ParserCombinators.Parsec.Pos
import Data.List (partition,find,elemIndices)
import Control.Applicative ((<|>))
import Data.Maybe (fromJust,isJust)

data TokenType = Operator | Identifier | Number | NewLine deriving (Show,Eq)
type Token = (String,TokenType,SourcePos)

--
splitByStart :: [String] -> [(Char,[String])]
splitByStart [] = []
splitByStart ((c:a):ss) = (c,a:map tail startWithc):splitByStart rest
            where (startWithc,rest) = partition ((==c).head) ss
splitByStart _ = error "does not expect the empty string"

data Tree = Tree [(Char,Tree)] (Maybe String) deriving Show


makeTree :: [String] -> Tree
makeTree = maketreeh ""

maketreeh :: [Char] -> [String] -> Tree
maketreeh current ss =  Tree (map (\ (c,xs)-> (c,maketreeh (c:current) xs)) (splitByStart longer) ) curnode
            where 
               (node,longer) = partition (=="") ss
               curnode = if node==[] then Nothing else Just (reverse current)

               
-- get the longest match
getFromTree :: Tree -> String -> Maybe (String,String)
getFromTree (Tree ts mx) "" = mx>>=(\x->Just (x,""))
getFromTree (Tree ts mx) s = (lookup (head s) ts >>= (\t -> getFromTree t (tail s))) 
            <|> (mx >>= (\x->Just (x,s)))

type Remainder = (String,SourcePos)
            
getq :: TokenType -> (String -> (String,String)) -> (Remainder -> ([Token],Remainder))
getq typ f (ss,p) = ([(t,typ,p)] , 
                 (rest, incSourceLine (if n==0 then incSourceColumn p c else setSourceColumn p (c+1)) n ))
        where
            (t,rest) = f ss 
            n = length $ elemIndices '\n' t
            c = length $ takeWhile (/='\n') $ reverse t


type Tgtrs = [(String -> Bool, Remainder -> ([Token],Remainder))]

tokengetters :: Tree -> [(String -> Bool, Remainder -> ([Token],Remainder))]
tokengetters t = [
            ((== '\n').head, getq NewLine $ \ss -> ("\n",tail ss)),
            (isSpace.head, \(ss,p) -> ([],(tail ss,incSourceColumn p 1))),
            (isJust.(getFromTree t), getq Operator (fromJust.(getFromTree t))),
            (isDigit.head, getq Number (break (not.isDigit))),
            (isAlpha.head, getq Identifier (break (\x->not (isAlphaNum x || x=='_'))))
            ]


tokeniseFromOps :: [String] -> String -> Either String [Token]
tokeniseFromOps ops' s = (tokeniseFromGetters $ tokengetters $ makeTree ops')  (s,initialPos "source")


tokeniseFromFile :: [String] -> String -> String -> Either String [Token]
tokeniseFromFile ops' fname s = (tokeniseFromGetters $ tokengetters $ makeTree ops')  (s,initialPos fname)


tokeniseFromGetters :: Tgtrs -> Remainder -> Either String [Token]
tokeniseFromGetters gs ("",_) = Right []
tokeniseFromGetters gs s = case find (\(x,_) -> x $ fst s) gs of
            Nothing -> Left ("error in tokeniser: " ++ (show $ snd s))
            Just (_,f) -> let (a,rest)=(f s) in (tokeniseFromGetters gs rest >>= Right . (a++))
            
        
