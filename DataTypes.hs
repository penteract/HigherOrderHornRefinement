module DataTypes where

import Data.Maybe(fromJust)
import Data.List

data Sort = Arrow Sort Sort
          | Int | Bool
    deriving (Eq)
    
instance Show Sort where
    show = prns
    
data MonoType = ArrowT Variable MonoType MonoType
          | IntT | BoolT Term 
    deriving (Eq)
    
type Scheme = ([(Variable,Sort)],MonoType)

instance Show MonoType where
    show t = prnty t


type Variable = String
type Constant = String
data Term = Variable Variable
          | Constant Constant
          | Apply Term Term
          | Lambda Variable Sort Term
          deriving (Eq)
          
instance Show Term where
    show = prnt

type DeltaEnv = [(Variable,Sort)]
type Gamma = [(Variable,Scheme)]


flat :: MonoType -> Sort
flat (ArrowT _ a b) = Arrow (flat a) (flat b)
flat IntT = Int
flat (BoolT _) = Bool

--symbols
logicalConstants = ["true","false"]

logicalUnary = ["¬"]
logicalBinary = ["⇒","∨","∧","⇔"]
logicalQuantifiers = ["∀","∃","λ"]
logicalSymbols = logicalUnary ++ logicalBinary ++ logicalQuantifiers ++ logicalConstants

ilaConstants = ["0","1"]
ilaOps = ["+","-"]
ilaRels = [">=","<=",">","<", "="]
binaryOps = ilaOps++ilaRels++logicalBinary


baseEnv = zip logicalBinary (repeat (Arrow Bool . Arrow Bool $ Bool)) ++
          zip logicalUnary (repeat (Arrow Bool Bool)) ++
          zip logicalConstants (repeat Bool)

ilaEnv :: DeltaEnv
ilaEnv = zip ilaOps (repeat (Arrow Int . Arrow Int $ Int)) ++
         zip ilaRels (repeat (Arrow Int . Arrow Int $ Bool)) ++
         zip ilaConstants (repeat Int) ++
         baseEnv


--printing functions

printt :: Term -> String
printt (Variable v) = v
printt (Constant c) = c
printt (Apply t1 t2) = '(' : printt t1 ++" "++ printt t2 ++ ")"
printt (Lambda v s t) = 'λ' :  v++":"++prints s++"."++ printt t 

prints :: Sort -> String
prints (Arrow a b) = '(' : prints a++ "->" ++ prints b ++ ")"
prints x = show x


prns :: Sort -> String
prns = prns' False

prns' :: Bool -> Sort -> String
prns' _ Int = "int"
prns' _ Bool = "bool"
prns' True x = parise $ prns' False x
prns' False (Arrow a b) = prns' True a++"->"++prns' False b

--prints nicely
prnt :: Term -> String
prnt t = prnt' 0 0 t

parise :: String->String
parise s = "("++s++")"

prnt' :: Int -> Int -> Term -> String
prnt' lp rp (Apply (Apply (Constant c) t1) t2)
    | c `elem` binaryOps = (\ (f,l,r) ->  f $ prnt' l p t1++" "++c++" "++prnt' p r t2)
                    (if p<=lp || p<rp then (parise,0,0) else (id,lp,rp))
        where p = fromJust $ lookup c getprec 
prnt' lp rp (Apply (Constant c) t) 
    | c `elem` logicalUnary = (let p=fromJust $ lookup c getprec in
                                   if p<rp then parise (c++prnt' p 0 t)
                                      else c++prnt' p rp t)
    | c `elem` logicalQuantifiers = case t of
        (Lambda a s body) -> (if rp==0 then id else parise) $
                                (c++a++":"++prns s++"."++prnt' 0 0 body)
        _ -> error "bad quantifier"
prnt' lp rp (Lambda a s body)  = (if rp==0 then id else parise) $
                                ("λ"++a++":"++prns s++"."++prnt' 0 0 body)
prnt' lp rp (Variable v)  = v
prnt' lp rp (Constant c)  = c
prnt' lp rp (Apply a b)  = if maxPrec<=lp 
                              then parise (prnt' 0 maxPrec a ++ " " ++prnt' maxPrec 0 b)
                              else  prnt' lp maxPrec a ++ " " ++prnt' maxPrec rp b

                              
prnsch :: Scheme -> String
prnsch ([],t) = prnty t
prnsch (ss,t) = "A "++intercalate " " (map (\(x,y)->x++":"++prns y) ss) ++ "." ++ prnty t

prnty :: MonoType -> String
prnty = prnty' False

prnty' _ IntT = "int"
prnty' _ (BoolT s) = "bool["++prnt s++"]"
prnty' b (ArrowT "_" t1 t2) =
    (if b then parise else id) (prnty' True t1 ++ "->" ++ prnty' False t2)
prnty' b (ArrowT x t1 t2) =
    (if b then parise else id) (x++":"++prnty' True t1 ++ "->" ++ prnty' False t2)


--Strip outermost universal quantifiers from a conjugation of terms
stripQuantifiers :: Term -> Term
stripQuantifiers (Apply (Apply (Constant "∧") t1) t2) =
    (Apply (Apply (Constant "∧") (stripQuantifiers t1)) (stripQuantifiers t2))
stripQuantifiers (Apply (Constant "∀") (Lambda x s t)) = stripQuantifiers t
stripQuantifiers x = x

simplify :: Term -> Term
simplify (Apply (Apply (Constant "∧") (Constant "true")) t) = simplify t
simplify (Apply (Apply (Constant "∧") t) (Constant "true")) = simplify t
simplify (Apply (Apply (Constant "⇒") (Constant "true")) t) = simplify t
simplify (Apply t1 t2) = Apply (simplify t1) (simplify t2)
simplify (Lambda x s t) = Lambda x s (simplify t)
simplify t = t

simp t = simp' t (simplify t) -- simp' <*> simplify
simp' t t'= if t==t' then t else simp t'


opsByPrec = map return logicalBinary ++ [logicalUnary,ilaRels,ilaOps]
getprec = getprec' 1 opsByPrec
getprec' n [] = []
getprec' n (ops:rest) = map (flip (,) n) ops ++ getprec' (n+1) rest
getprec2 = foldl (++) [] (map (uncurry $ map. flip (,)) (zip [1..] opsByPrec))
maxPrec = length opsByPrec + 1


printLong :: Term -> String --prints conjunctive terms on separate lines
printLong (Apply (Apply (Constant "∧") t1) t2) = printLong t1 ++ '\n':printLong t2
printLong x = prnt x

printOut = printLong.simp.stripQuantifiers

pprint = putStrLn.printLong.simp.stripQuantifiers

aand t1 t2 = (Apply (Apply (Constant "∧") t1) t2)
aforall x s t = (Apply (Constant "∀") (Lambda x s t))