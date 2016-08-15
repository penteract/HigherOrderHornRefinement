module DataTypes(
    Term(Variable,Constant,Apply,Lambda),Sort(Int,Bool,Arrow),Env,
    printt,prnt,prints,
    ilaOps,ilaRels,logicalBinary,
    logicalConstants,logicalQuantifiers,logicalUnary,
    logicalSymbols,
    baseEnv,ilaEnv
    )where

import Data.Maybe(fromJust)

data Sort = Arrow Sort Sort
          | Int | Bool
    deriving (Show,Eq)

type Variable = String
type Constant = String
data Term = Variable Variable
          | Constant Constant
          | Apply Term Term
          | Lambda Variable Sort Term
          deriving (Show,Eq)


printt :: Term -> String
printt (Variable v) = v
printt (Constant c) = c
printt (Apply t1 t2) = '(' : printt t1 ++" "++ printt t2 ++ ")"
printt (Lambda v s t) = 'λ' :  v++":"++prints s++"."++ printt t 

prints :: Sort -> String
prints (Arrow a b) = '(' : prints a++ "->" ++ prints b ++ ")"
prints x = show x

prns :: Bool -> Sort -> String
prns _ Int = "Int"
prns _ Bool = "Bool"
prns True x = parise $prns False x
prns False (Arrow a b) = prns True a++"->"++prns False b

prnt :: Term -> String
prnt t = prnt' 0 0 t

parise :: String->String
parise s = "("++s++")"

prnt' :: Int -> Int -> Term -> String
prnt' lp rp (Apply (Apply (Constant c) t1) t2)
    | c `elem` binaryOps = if p<=lp || p<rp 
                              then parise (prnt' 0 p t1++c++prnt' p 0 t2)
                              else (prnt' lp p t1++c++prnt' p rp t2)
        where p = fromJust $ lookup c getprec 
prnt' lp rp (Apply (Constant c) t) 
    | c `elem` logicalUnary = (let p=fromJust $ lookup c getprec in
                                   if p<rp then parise (c++prnt' p 0 t)
                                      else c++prnt' p rp t)
    | c `elem` logicalQuantifiers = case t of
        (Lambda a s body) -> (if rp==0 then id else parise) $
                                (c++a++":"++prns False s++"."++prnt' 0 0 body)
        _ -> error "bad quantifier"
prnt' lp rp (Lambda a s body)  = (if rp==0 then id else parise) $
                                ("λ"++a++":"++prns False s++"."++prnt' 0 0 body)
prnt' lp rp (Variable v)  = v
prnt' lp rp (Constant c)  = c
prnt' lp rp (Apply a b)  = if maxPrec<=lp 
                              then parise (prnt' 0 maxPrec a ++ " " ++prnt' maxPrec 0 b)
                              else  prnt' lp maxPrec a ++ " " ++prnt' maxPrec rp b


logicalConstants = ["true","false"]--not used at the moment

logicalUnary = ["¬"]
logicalBinary = ["⇒","∨","∧","⇔"]
logicalQuantifiers = ["∀","∃","λ"]
logicalSymbols = logicalUnary ++ logicalBinary ++ logicalQuantifiers

ilaOps = ["+","-"]
ilaRels = [">=","<=",">","<", "="]

binaryOps = ilaOps++ilaRels++logicalBinary

opsByPrec = map return logicalBinary ++ [logicalUnary,ilaRels,ilaOps]
getprec = getprec' 1 opsByPrec
getprec' n [] = []
getprec' n (ops:rest) = map (flip (,) n) ops ++ getprec' (n+1) rest

maxPrec = length opsByPrec + 1

type Env = [(Variable,Sort)]
            
baseEnv = zip logicalBinary (repeat (Arrow Bool . Arrow Bool $ Bool)) ++
          zip logicalUnary (repeat (Arrow Bool Bool)) ++
          zip logicalConstants (repeat Bool)

ilaEnv :: Env
ilaEnv = zip ilaOps (repeat (Arrow Int . Arrow Int $ Int)) ++
         zip ilaRels (repeat (Arrow Int . Arrow Int $ Bool)) ++
         [("0",Int), ("1",Int)] ++ baseEnv
