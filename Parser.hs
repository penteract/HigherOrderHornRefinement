{-

-}
module Parser where

import Tokeniser

import Text.Parsec.Prim
import Text.Parsec.Combinator

import Data.Char
import Data.Maybe
import Data.List(sortBy)
import Data.Ord(comparing)
import DataTypes
import Control.Applicative((<**>))

sortOn f = map snd . sortBy (comparing fst) . map (\x -> let y = f x in y `seq` (y, x))

exists = "∃"
forall = "∀"

--get rid of unicode from output
legiblise "" _ _ = ""
legiblise (c:s) [] l = c:legiblise s l l
legiblise s ((x,y):xs) l = if start == y then x ++ legiblise end l l else legiblise s xs l
    where (start,end)= splitAt (length y) s

ll= sortOn (negate.length.snd) [ ("^","∧"), ("=>","⇒"), ("\\","λ"),("A ","∀"),("E ","∃"), ("\\/","∨"),("<=>","⇔")]

ununicode :: String -> String
ununicode s= legiblise s ll ll

cannonicals :: [(String,String)]
cannonicals = ll ++[("≤","<="),("≥",">="),("−","-"),("→","->")]

--Parser
---------------

--setup

typeSymbols = ["->"]

symbols :: [String]
symbols = logicalSymbols ++ ilaOps ++ ilaRels++ typeSymbols
    ++ ["(",")",":",".",",",";","[","]"] ++ ["program","goal","environment"]
    -- ++ ["environment","program","goal"]

cannonise :: Token -> Token
cannonise (x,Operator,pos) = (fromMaybe x (lookup x cannonicals),Operator,pos)
cannonise (x,Identifier,pos) = fromMaybe (x,Identifier,pos) (lookup x cannonicals >>= \o->Just (o,Operator,pos))
cannonise x = x

type MyParser a = Parsec [Token] () a

--Get a single token if it matches a predicate
testTok :: (Token-> Bool) -> MyParser String
testTok p = token (\(a,b,c)->a)
            (\(a,b,c)->c)
            (\ (a,b,c)-> if p (a,b,c) then Just a else Nothing)

testStr :: (String-> Bool) -> MyParser String
testStr p = testTok (\(s,_,_)->p s)

tok :: String -> MyParser String
tok s = testStr (==s)

oneOf :: [String] -> MyParser String
oneOf [] = fail "not in set"
oneOf (s:ss) = tok s <|> oneOf ss


-- parse a sequence of left assoc binary operators in order of precedence (where some share precedence)
opPrecl :: [[String]] -> MyParser Term -> MyParser Term
opPrecl [] p = p
opPrecl (ss:rest) p = chainl1 (opPrecl rest p)
                                 (do op <- (oneOf ss <?> "operator")
                                     return (\ a b -> Apply (Apply (Constant op) a) b))


parens :: MyParser a -> MyParser a
parens p = do tok "("
              t <- p
              tok ")"
              return t

number :: MyParser Term
number = testTok (\ (_,t,_) ->t==Number) >>= return.Constant

variable :: MyParser Term
variable = testTok (\ (_,t,_) ->t==Identifier) >>= return.Variable

logicalConstant ::MyParser Term
logicalConstant = testTok (\ (s,t,_) -> (t==Operator) && (s`elem`logicalConstants)) >>= return.Constant

int :: MyParser Sort
int = (tok "int" <|> tok "Int") >> return Int
bool:: MyParser Sort
bool = (tok "bool" <|> tok "Bool") >> return Bool

sort :: MyParser Sort
sort = chainr1 (int <|> bool <|> parens sort)
                (tok "->" >> return Arrow)

vlist :: MyParser [Term]
vlist = chainl1 (variable >>= return.return) (tok "," >> return (++))

monotype :: MyParser MonoType
monotype = chainr1 (
           (do _ <- bool
               tok "["
               g <- formula
               tok "]"
               return $ BoolT g) <|>
           (do (Variable x)<-variable
               tok ":"
               _ <- int
               tok "->"
               ty <- monotype
               return $ ArrowT x IntT ty)<|>
           parens monotype)
           (tok "->" >> return (ArrowT "_"))



simpleTerm :: MyParser Term
simpleTerm = parens formula
         <|> logicalConstant
         <|> number
         <|> variable

simpleFormula :: MyParser Term
simpleFormula = (many1 simpleTerm >>= return . foldl1 Apply)


tvlist :: MyParser [(Sort,Term)]
tvlist = do x<-chainl1
                (do vs<-vlist
                    (tok ":")
                    s<-sort
                    return $ map ((,) s) vs)
                (tok ",">>return (++))
            tok "."
            return x

fromtvlist :: String -> [(Sort,Term)] -> Term -> Term
fromtvlist _ [] body = body
fromtvlist q ((s,Variable v):tvs) body = (if q=="λ" then id else Apply (Constant q))
                    (Lambda v s (fromtvlist q tvs body))

negation = (tok "¬" >> (quantified <|> negation) >>= return.(Apply (Constant "¬")))
       <|> opPrecl [ilaRels,ilaOps] simpleFormula


quantified :: MyParser Term
quantified = (try (do q <- oneOf logicalQuantifiers
                      tvs <- tvlist
                      return $ fromtvlist q tvs)
              <|> (do tok "∃"
                      (Variable v) <- variable
                      tok ":"
                      ty <- monotype
                      tok "."
                      return (ExistsT v ty))) --Really don't want to do reduction here
    <*> formula


formula :: MyParser Term
formula = quantified
      <|> opPrecl (map return logicalBinary) negation
      <?> "formula"

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
    ts <- tokeniseFromFile (symbols ++ map fst cannonicals) fname contents
    let body = map cannonise ts
    runParser file () fname body)

fromParse (Left x) = Left $ show x
fromParse (Right x) =  Right x

--for testing
qp =  (>>= (runParser formula () "" . map cannonise)) . tokeniseFromOps  (symbols ++ map fst cannonicals)
