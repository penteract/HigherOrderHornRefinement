module Simplify(stripQuantifiers,simp,printOut,pprint,proc)
    where

import DataTypes
import Transform(vlist)

--import Data.Maybe(fromJust,fromMaybe)
import Data.List
import Tools

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
simplify (Apply (Constant "∀") (Lambda x s (Constant "true"))) = (Constant "true")
simplify (Apply t1 t2) = Apply (simplify t1) (simplify t2)
simplify (Lambda x s t) = Lambda x s (simplify t)
simplify t = t

simp t = simp' t (simplify t) -- simp' <*> simplify
simp' t t'= if t==t' then t else simp t'

printOut = printLong.simp.stripQuantifiers

pprint = putStrLn.printLong.simp.stripQuantifiers

type Clause = (Term,([String],String))

-- given a conjunctions of implications, apply the unfold simplification
-- do not unfold the other variables given

proc :: Term -> [Variable] -> Term
proc t preserved = unpreproc $ f preserved [] ks
    where (ks,vss) = preproc t

unpreproc :: [Clause] -> Term
unpreproc = foldl1 aand . map (\ (t,(xs,v)) ->
  aimplies t (foldl Apply (Variable v) (map Variable xs)))

--get into a reasonably nice format
-- assume it's safe to pull all quantifiers to the front
preproc :: Term -> ([Clause],[(Variable,Sort)])
preproc (Apply (Apply (Constant "∧") t1) t2) = (k1s++k2s, v1s `union` v2s)
    where
        (k1s,v1s) = preproc t1
        (k2s,v2s) = preproc t2
preproc (Apply (Apply (Constant "⇒") t1) t2) = ([(t1,fromRight$vlist t2)],[])
preproc (Apply (Constant "∀") (Lambda x s t)) = (ks,(x,s):vs)
    where (ks,vs) = preproc t
preproc x = error (show x)


-- Assumes the input list of clauses contains at most 1 instance of each variable as a head
f :: [Variable] -> [Clause] -> [Clause] -> [Clause]
f vs ks [] = ks
f vs ks1 ((body,(params,headvar)):ks2) = if headvar `elem` vs || headvar `elem` freeVars body
    then f vs ((body,(params,headvar)):ks1) ks2
    else f vs (map sub ks1) (map sub ks2)
    where sub = \(x,y) -> (subs (body,(params,headvar)) [] x, y)

subs :: Clause -> [Term] -> Term -> Term
subs (body,(params,v)) args (Variable x) = if x==v
    then if length args < length params
        then error ("too few arguments to "++x)
        else foldl (Apply) (replaceInTerm (zip params args) body) (drop (length params) args)
    else foldl (Apply) (Variable x) args
subs k args (Apply t1 t2) = subs k (subs k [] t2:args) t1
subs k args (Lambda x s t) = foldl (Apply) (Lambda x s (subs k [] t)) args
subs k args (Constant c) = foldl (Apply) (Constant c) args
