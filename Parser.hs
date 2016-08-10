module Parser where

import Text.ParserCombinators.Parsec.Combinator
import Text.ParserCombinators.Parsec.Prim
import Text.Parsec.Prim(parserReturn)
--import Text.Parsec
--import Text.Parsec.Prim
import Data.Char
import Tokeniser
import Data.Maybe
import DataTypes


exists = "∃"
forall = "∀"

(.>) :: Monad m =>  (b -> m a) -> (a->c) -> b -> m c
(.>) xm f y = (xm y) >>= return.f

cannonicals :: [(String,String)]
cannonicals = [ ("^","∧"), ("=>","⇒"), ("\\","λ"),("A","∀"),("E","∃"),("≤","<="),
    ("−","-"),("→","->"),("\\/","∨")]

--Parser    

--setup 

typeSymbols = ["->"]

symbols :: [String]
symbols = logicalSymbols ++ ilaOps ++ ilaRels++ typeSymbols ++["(",")",":","."] ++ map fst cannonicals

cannonise :: Token -> Token
cannonise (x,Operator,pos) = (fromMaybe x (lookup x cannonicals),Operator,pos)
cannonise x = x

tknsr = tokeniseFromOps symbols
tknsr2 s = tknsr s >>= return.map cannonise

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

parser :: MyParser [Term]
parser = do res <- chainl lineParser (tok "\n" >> return (++)) []
            eof
            return res

lineParser :: MyParser [Term]
lineParser = (formula >>= return.return)
         <|> parserReturn []
formula :: MyParser Term
formula = quantified
      <|> opPrecl (map return logicalBinary) negation
      <?> "formula"

test2 = "Af:Int->(Int->Int).Eg:Int->Int.¬ En:Int.f n = g"
negation = (tok "¬" >> (quantified <|> negation) >>= return.(Apply (Constant "¬")))
       <|> opPrecl [ilaOps,ilaRels] simpleFormula


quantified :: MyParser Term
quantified = do q <- oneOf logicalQuantifiers
                Variable v <- variable
                tok ":"
                t <- sort
                tok "."
                body <- formula
                return $ (if q=="λ" then id else Apply (Constant q))
                    (Lambda v t body)

simpleFormula :: MyParser Term
simpleFormula = (many1 simpleTerm >>= return . foldl1 Apply)

simpleTerm :: MyParser Term
simpleTerm = parens formula
         <|> number
         <|> variable
         

number :: MyParser Term
number = testTok (\ (_,t,_) ->t==Number) >>= return.numToTerm.read
variable = testTok (\ (_,t,_) ->t==Identifier) >>= return.Variable

sort :: MyParser Sort
sort = chainr1 ((tok "Int" >> return Int) <|> (tok "Bool" >> return Bool) <|> parens sort)
                (tok "->" >> return Arrow)


--functions to help display the result of the parser

-- Example string: "∀cabr. Row FullAdder c a b r ⇒ RipCarry c a b r"
-- ∀f:Int->Int->Bool. ∃x:Int. ¬(n ≤ 0) ∧ Iter f x (n − 1) r ∧ f m x ⇒ Iter f m n r
tests = "∀r:Int.∀n:Int.∀m:Int.∀Iter:(Int->Int->Bool)->Int->Int->Int->Bool.∀f:Int->Int->Bool. ∃x:Int. ¬(n <= 0) ∧ Iter f x (n - 1) r ∧ f m x ⇒ Iter f m n r"


fromRight :: Either a b -> b
fromRight (Right x) = x

fromLeft :: Either a b -> a
fromLeft (Left x) = x

fromEither :: Either a a -> a
fromEither (Left x) = x
fromEither (Right x) = x


fromParse (Left x) = show x
fromParse (Right x) =  x
fromParse2 (Left x) = Left $ show x
fromParse2 (Right x) =  Right x

fp (Left x) = Left $ show x
fp (Right x)  = (Right x)

qshow s = putStrLn $ fromEither (tknsr2 s >>= (\ x->return $ fromParse (
            runParser parser () "" x >>= return.concat.map (++"\n").map prnt)))

runp s=  tknsr2 s >>= fromParse2. runParser parser () ""            


test3 = "y = x + 1 ⇒ Succ x y\n"++
    "n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "∃x:Int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x ⇒ Iter f m n r\n"
test4 = "Ax:Int.Ay:Int.y = x + 1 ⇒ Succ x y\n"++
    "An:Int.Am:Int.Af:Int->Int->Bool.n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "∃x:Int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x ⇒ Iter f m n r\n"