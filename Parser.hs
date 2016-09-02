module Parser where

import Text.ParserCombinators.Parsec.Combinator
import Text.ParserCombinators.Parsec.Prim
import Text.Parsec.Prim(parserReturn)
--import Text.Parsec
--import Text.Parsec.Prim
import Data.Char
import Tokeniser
import Data.Maybe
import Data.List(sortBy)
import Data.Ord(comparing)
import DataTypes
import Tools

sortOn f = map snd . sortBy (comparing fst) . map (\x -> let y = f x in y `seq` (y, x))

exists = "∃"
forall = "∀"

(.>) :: Monad m =>  (b -> m a) -> (a->c) -> b -> m c
(.>) xm f y = (xm y) >>= return.f

--get rid of unicode from output
legiblise "" _ _ = ""
legiblise (c:s) [] l = c:legiblise s l l
legiblise s ((x,y):xs) l = if start == y then x ++ legiblise end l l else legiblise s xs l
    where (start,end)= splitAt (length y) s

ll= sortOn (negate.length.snd) [ ("^","∧"), ("=>","⇒"), ("\\","λ"),("A ","∀"),("E ","∃"), ("\\/","∨"),("<=>","⇔")]

ununicode :: String -> String
ununicode s= legiblise s ll ll

cannonicals :: [(String,String)]
cannonicals = ll ++[ ("≤","<="),("−","-"),("→","->")]

--Parser    

--setup 

isWord w = w=="" || (isAlpha (head w) && (all (\c->isAlphaNum c||c=='_') w))

typeSymbols = ["->"]

symbols :: [String]
symbols = logicalSymbols ++ ilaOps ++ ilaRels++ typeSymbols
    ++ ["(",")",":",".",",",";"]
    -- ++ ["environment","program","goal"]

cannonise :: Token -> Token
cannonise (x,Operator,pos) = (fromMaybe x (lookup x cannonicals),Operator,pos)
cannonise (x,Identifier,pos) = fromMaybe (x,Identifier,pos) (lookup x cannonicals >>= \o->Just (o,Operator,pos))
cannonise x = x

tknsr = tokeniseFromOps symbols
tknsr2 s = tokeniseFromOps (filter (not.isWord) (symbols ++ map fst cannonicals)) s >>= return.map cannonise

type MyParser a = GenParser Token () a
    
--get a single token if it matches a predicate
testTok :: (Token-> Bool) -> MyParser String
testTok p = token (\(a,b,c)->a)
            (\(a,b,c)->c)
            (\ (a,b,c)-> if p (a,b,c) then Just a else Nothing)

testStr :: (String-> Bool) -> MyParser String
testStr p = testTok (\(s,_,_)->p s)

tok :: String -> MyParser String
tok s = testStr (==s)

numToTerm 0 = Constant "0"
numToTerm 1 = Constant "1"
numToTerm n = if n<0 then Apply (Apply (Constant "-") (Constant "0")) (numToTerm (-n))
                     else Apply (Apply (Constant "+") (Constant "1")) (numToTerm (n-1))

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
number = testTok (\ (_,t,_) ->t==Number) >>= return.numToTerm.read

variable :: MyParser Term
variable = testTok (\ (_,t,_) ->t==Identifier) >>= return.Variable

sort :: MyParser Sort
sort = chainr1 ((tok "int" >> return Int) <|> (tok "bool" >> return Bool) <|> parens sort)
                (tok "->" >> return Arrow)

vlist :: MyParser [Term]
vlist = chainl1 (variable >>= return.return) (tok "," >> return (++))

simpleTerm :: MyParser Term
simpleTerm = parens formula
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
quantified = do q <- oneOf logicalQuantifiers
                tvs <- tvlist
                body <- formula
                return $ fromtvlist q tvs body

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



environment :: MyParser DeltaEnv
environment = chainl (do
    (Variable v) <- variable
    tok ":"
    s<-sort
    return [(v,s)])
    (tok "\n">>return (++)) []

separator = tok ";" >> tok "\n"

file :: MyParser (DeltaEnv,[Term],Term)
file = do
    tok "environment" >> tok "\n"
    d <- environment
    separator >> tok "program" >> tok "\n"
    prog <- chainl lineParser (tok "\n" >> return (++)) []
    separator >> tok "goal" >> tok "\n"
    goal <- formula
    eof <|> ((tok "\n" <|> separator <|> tok ";") >> eof)
    return (d,prog,goal)


parseFile :: String -> String -> Either String (DeltaEnv,[Term],Term)
parseFile fname contents = do
    ts <- tokeniseFromFile (symbols ++ map fst cannonicals) fname contents
    let body = strip (map cannonise ts)
    fromParse $ runParser file () fname body
    where
        strip [] = []
        strip (("\n",NewLine,_):rest) = strip rest
        strip (c:rest) = c:strip' rest
        strip' (("\n",NewLine,p):rest) = ("\n",NewLine,p) : strip rest
        strip' x = strip x

strip [] = []
strip (("\n",NewLine,_):rest) = strip rest
strip (c:rest) = c:strip' rest
strip' (("\n",NewLine,p):rest) = ("\n",NewLine,p) : strip rest
strip' x = strip x

--functions to help display the result of the parser 

fromParse (Left x) = Left $ show x
fromParse (Right x) =  Right x


fromLeft :: Either a b -> a
fromLeft (Left x) = x

fromEither :: Either a a -> a
fromEither (Left x) = x
fromEither (Right x) = x



qshow s = putStrLn $ fromEither (tknsr2 s >>= (\ x-> fromParse (
            runParser parser () "" x >>= return.concat.map (++"\n").map prnt)))
qshowl s = putStrLn $ ununicode $ fromEither (tknsr2 s >>= (\ x-> fromParse (
            runParser parser () "" x >>= return.concat.map (++"\n").map prnt)))
qshowl2 s = putStrLn $ ununicode $ fromEither (tknsr2 s >>= (\ x-> fromParse (
            runParser parser () "" x >>= return.concat.map (++"\n").map printt)))

qp = fromRight . runParser formula () "" . fromRight.tknsr2
            
runp s=  tknsr2 s >>= fromParse. runParser parser () "" 


qt s = fromRight $ (runParser parser () "" (fromRight $ tknsr2 s))
qs s = fromRight $ (runParser sort () "" (fromRight $ tknsr2 s))