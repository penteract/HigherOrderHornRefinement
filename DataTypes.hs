module DataTypes where

import Data.Maybe(fromJust,fromMaybe)
import Data.List
import Tools

--Datatype definitions
---------------
data Sort = Arrow Sort Sort
          | Int | Bool
    deriving (Eq)

instance Show Sort where
    show = prns

data MonoType = ArrowT Variable MonoType MonoType
          | IntT | BoolT Term 
    deriving (Eq)

--type Scheme = ([(Variable,Sort)],MonoType)

instance Show MonoType where
    show t = prnty t


type Variable = String
type Constant = String
data Term = Variable Variable
          | Constant Constant
          | Apply Term Term
          | Lambda Variable Sort Term
          | ExistsT Variable MonoType Term
          deriving (Eq)

instance Show Term where
    show = prnt

type DeltaEnv = [(Variable,Sort)]
type Gamma = [(Variable,MonoType)]


--functions for working with DataTypes
---------------


--Gives the sort corresponding to a monotype
flat :: MonoType -> Sort
flat (ArrowT _ a b) = Arrow (flat a) (flat b)
flat IntT = Int
flat (BoolT _) = Bool

-- replaces all unbound occurences of a variable in a MonoType
-- this affects instances of Bool<t>
replaceInMT :: [(Variable,Term)] -> MonoType -> MonoType
replaceInMT rs IntT = IntT
replaceInMT rs (BoolT t) = BoolT (replaceInTerm rs t)
replaceInMT rs (ArrowT x t1 t2) = --may cause problems if a variable in rs becomes bound
    ArrowT x (replaceInMT rs t1) (replaceInMT rs_ t2)
    where rs_ = filter (\(a,b) -> a/=x) rs

replaceInTerm :: [(Variable,Term)] -> Term -> Term
replaceInTerm rs (Apply t1 t2) = Apply (replaceInTerm rs t1) (replaceInTerm rs t2)
replaceInTerm rs (Lambda x s t) = --may cause problems if a variable in rs becomes bound
    Lambda x s (replaceInTerm (filter (\(a,b) -> a/=x) rs) t)
replaceInTerm rs (Variable v) = fromMaybe (Variable v) (lookup v rs)
replaceInTerm rs (Constant c) = (Constant c)

-- separate leading quantifiers from a term
getQuants :: Term -> ([(Variable,Sort)],Term)
getQuants (Apply (Constant "∀") (Lambda x s t)) = ((x,s):vss, t1) where (vss,t1) = getQuants t
getQuants x = ([],x)

--List the free variables in a term
freeVars :: Term -> [Variable]
freeVars (Variable x) = [x]
freeVars (Constant _) = []
freeVars (Apply t1 t2) = union (freeVars t1) (freeVars t2)
freeVars (Lambda x s t) = filter (/=x) $ freeVars t

freeVarsOfTy :: MonoType -> [Variable]
freeVarsOfTy = freeVarsOfTy' []

freeVarsOfTy' :: [Variable] -> MonoType -> [Variable]
freeVarsOfTy' xs IntT = []
freeVarsOfTy' xs (BoolT t) = freeVars t \\ xs
freeVarsOfTy' xs (ArrowT x t1 t2) = union x1s x2s
    where x1s = freeVarsOfTy' xs t1
          x2s = freeVarsOfTy' (x:xs) t2


--symbols
---------------
logicalConstants = ["true","false"]

logicalUnary = ["¬"]
logicalBinary = ["⇒","∨","∧","⇔"]
logicalQuantifiers = ["∀","∃","λ"]
logicalSymbols = logicalUnary ++ logicalBinary ++ logicalQuantifiers ++ logicalConstants

ilaConstants = ["0","1"]
ilaOps = ["+","-"]
ilaRels = [">=","<=",">","<", "="]
binaryOps = ilaOps++ilaRels++logicalBinary

isIlaSymbol :: String -> Bool
isIlaSymbol s = s `elem` (ilaOps++ilaRels++ilaConstants++logicalConstants)


baseEnv = zip logicalBinary (repeat (Arrow Bool . Arrow Bool $ Bool)) ++
          zip logicalUnary (repeat (Arrow Bool Bool)) ++
          zip logicalConstants (repeat Bool)

ilaEnv :: DeltaEnv
ilaEnv = zip ilaOps (repeat (Arrow Int . Arrow Int $ Int)) ++
         zip ilaRels (repeat (Arrow Int . Arrow Int $ Bool)) ++
         zip ilaConstants (repeat Int) ++
         baseEnv


--printing functions
---------------

--prints in detail
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
prns' _ Int = "Int"
prns' _ Bool = "Bool"
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

      {-                        
prnsch :: Scheme -> String
prnsch ([],t) = prnty t
prnsch (ss,t) = "A "++intercalate " " (map (\(x,y)->x++":"++prns y) ss) ++ "." ++ prnty t
    -}

prnty :: MonoType -> String
prnty = prnty' False

prnty' _ IntT = "Int"
prnty' _ (BoolT s) = "Bool["++prnt s++"]"
prnty' b (ArrowT "_" t1 t2) =
    (if b then parise else id) (prnty' True t1 ++ "->" ++ prnty' False t2)
prnty' b (ArrowT x t1 t2) =
    (if b then parise else id) (x++":"++prnty' True t1 ++ "->" ++ prnty' False t2)

opsByPrec = map return logicalBinary ++ [logicalUnary,ilaRels,ilaOps]
getprec = getprec' 1 opsByPrec
getprec' n [] = []
getprec' n (ops:rest) = map (flip (,) n) ops ++ getprec' (n+1) rest
getprec2 = foldl (++) [] (map (uncurry $ map. flip (,)) (zip [1..] opsByPrec))
maxPrec = length opsByPrec + 1

printLong :: Term -> String --prints conjunctive terms on separate lines
printLong (Apply (Apply (Constant "∧") t1) t2) = printLong t1 ++ '\n':printLong t2
printLong x = prnt x

--helpful constructors
aand t1 t2 = (Apply (Apply (Constant "∧") t1) t2)
aor t1 t2 = (Apply (Apply (Constant "∨") t1) t2)
aforall x s t = (Apply (Constant "∀") (Lambda x s t))
aimplies t1 t2 = (Apply (Apply (Constant "⇒") t1) t2)
aexists x s t = (Apply (Constant "∃") (Lambda x s t))
