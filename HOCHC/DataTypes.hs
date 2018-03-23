{-
Defines the basic data types such as sorts, terms and types.
See Chapters 2 and 4.

Includes functions needed to make instances of Show, as well as
common definitions used to construct and manipulate formulas.
-}

module HOCHC.DataTypes where

import Data.Maybe(fromJust,fromMaybe)
import Data.List
import Data.Char(toLower)
import Control.Applicative(liftA2)

--Datatype definitions
---------------
data Sort = Arrow Sort Sort
          | Int | Bool
    deriving (Eq)

instance Show Sort where
    show = prns


type Variable = String
type Constant = String
data Term = Variable Variable
          | Constant Constant
          | Apply Term Term
          | If Term Term Term -- condition, then, else
          --those below are not currently supported as input
          | Lambda Variable Sort Term
          | ExistsT Variable MonoType Term --Type guards (Section 4.3)
          deriving (Eq)

instance Show Term where
    show = prnt

type Definition = (Variable, [Variable], Term)

--Note that a monotype is simply called a type in the report
data MonoType = ArrowT Variable MonoType MonoType
          | IntT | BoolT Term
    deriving (Eq)

instance Show MonoType where
    show = prnty

type DeltaEnv = [(Variable,Sort)] --sort environment
type Gamma = [(Variable,MonoType)] --type environment


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


--Symbols
---------------
logicalConstants = ["true","false"]

--assignmentOp = ":="

logicalUnary = ["¬"]
logicalBinary = ["⇒","∨","∧","⇔"]
quantifiers = ["λ"]
logicalQuantifiers = ["∃","∀"]
logicalSymbols = logicalUnary ++ logicalBinary ++ logicalConstants ++ logicalQuantifiers
constants = "assert":logicalConstants

ilaOps = ["+","-"]
ilaRels = [">=","<=",">","<", "=", "≠"]
binaryOps = ilaOps++ilaRels++logicalBinary

isIlaSymbol :: String -> Bool
isIlaSymbol = liftA2 (||) (`elem` (ilaOps++ilaRels++logicalConstants)) isIntegerConstant

isIntegerConstant :: String -> Bool
isIntegerConstant = all (`elem` ['0'..'9'])

--is the symbol a non relational ILA symbol
isIlaFn :: String -> Bool
isIlaFn = liftA2 (||) (`elem` (ilaOps)) isIntegerConstant

baseEnv = zip logicalBinary (repeat (Arrow Bool . Arrow Bool $ Bool)) ++
          zip logicalUnary (repeat (Arrow Bool Bool)) ++
          zip logicalConstants (repeat Bool)

ilaEnv :: [(Constant,Sort)] --DeltaEnv
ilaEnv = zip ilaOps (repeat (Arrow Int . Arrow Int $ Int)) ++
         zip ilaRels (repeat (Arrow Int . Arrow Int $ Bool)) ++
         baseEnv

mainEnv = [("assert", Arrow Bool Bool)] ++ ilaEnv

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
prints x = prns x


--somewhat inefficient
prns = map toLower . prnS

--prints nicely
prnS :: Sort -> String
prnS = prnS' False

prnS' :: Bool -> Sort -> String
prnS' _ Int = "Int"
prnS' _ Bool = "Bool"
prnS' True x = parise $ prnS' False x
prnS' False (Arrow a b) = prnS' True a++"->"++prnS' False b

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
                                (c++a++":"++prns s++". "++prnt' 0 0 body)
        _ -> error "bad quantifier"
prnt' lp rp (Lambda a s body)  = (if rp==0 then id else parise) $
                                ("λ"++a++":"++prns s++"."++prnt' 0 0 body)
prnt' lp rp (Variable v)  = v
prnt' lp rp (Constant c)  = c
prnt' lp rp (Apply a b)  = if maxPrec<=lp
                              then parise (prnt' 0 maxPrec a ++ " " ++prnt' maxPrec 0 b)
                              else  prnt' lp maxPrec a ++ " " ++prnt' maxPrec rp b
prnt' lp rp (If cond thn els) = (if rp==0 then id else parise) $
                                   "if "++prnt' 0 0 cond
                                 ++" then "++prnt' 0 0 thn
                                 ++" else "++prnt' 0 0 els


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

--apply a (typically recursive) function  uniformly across unchecked cases
appdown :: (Term -> Term) -> Term -> Term
appdown f (Lambda v s t) = (Lambda v s (f t))
appdown f (Apply a b) = Apply (f a) (f b)
appdown f (ExistsT v ty t) = (ExistsT v ty (f t))
appdown f (If c t1 t2) = If (f c) (f t1) (f t2)
appdown f t = t --Variable or Constant

-- Helpful constructors (apply 'and', apply 'or', etc)
aand t1 t2 = (Apply (Apply (Constant "∧") t1) t2)
aor t1 t2 = (Apply (Apply (Constant "∨") t1) t2)
aforall x s t = (Apply (Constant "∀") (Lambda x s t))
aimplies t1 t2 = (Apply (Apply (Constant "⇒") t1) t2)
aequals t1 t2 = (Apply (Apply (Constant "=") t1) t2)
aexists x s t = (Apply (Constant "∃") (Lambda x s t))
