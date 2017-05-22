{-
This module contains a number of operations for reducing the output
e.g. turning 'x ^ true' into 'x'
-}

module Simplify(pullOutAllQuantifiers,stripQuantifiers,simp,proc)
    where

import DataTypes
import Transform(vlist,occursIn)
import Data.List
import Tools


--Strip outermost universal quantifiers from a conjugation of terms
--the difference between this and (uncurry unpreproc.preproc) is that this deals with existential quantifiers
--Not correct in general, but works in a system of Horn clauses when variables with a particular name are not bound more than once within the same clause
pullOutAllQuantifiers :: Bool -> Term -> (Term,[(String,Sort)])
pullOutAllQuantifiers b (Apply (Apply (Constant c) t1) t2)
    | c `elem` ["⇒","∨","∧"] = (Apply (Apply (Constant c) t1') t2', vs1 `union` vs2)
        where (t1',vs1) = pullOutAllQuantifiers (b `xor` (c=="⇒")) t1
              (t2',vs2) = pullOutAllQuantifiers b t2
pullOutAllQuantifiers b (Apply (Constant "¬") t) = ((Apply (Constant "¬") t'),vs)
    where (t',vs) = pullOutAllQuantifiers (not b) t
pullOutAllQuantifiers True (Apply (Constant "∀") t) = case t of
        (Lambda x ty body) -> fmap (((x,ty):) . delete (x,ty)) $ pullOutAllQuantifiers True body
        _ -> error "bad quantifier"
pullOutAllQuantifiers False (Apply (Constant "∀") t) = case t of
        _ -> error "bad quantifier"
pullOutAllQuantifiers False (Apply (Constant "∃") t) = case t of
        (Lambda x ty body) -> fmap (((x,ty):) . delete (x,ty)) $ pullOutAllQuantifiers False body
        _ -> error "bad quantifier"
pullOutAllQuantifiers True (Apply (Constant "∃") t) = case t of
        _ -> error "bad quantifier"
pullOutAllQuantifiers b t = (t,[])

stripQuantifiers :: Term -> Term
stripQuantifiers (Apply (Apply (Constant "∧") t1) t2) =
    (Apply (Apply (Constant "∧") (stripQuantifiers t1)) (stripQuantifiers t2))
stripQuantifiers (Apply (Constant "∀") (Lambda x s t)) = stripQuantifiers t
stripQuantifiers x = x

simplify :: Term -> Term
simplify (Apply (Apply (Constant "∧") (Constant "true")) t) = simplify t
simplify (Apply (Apply (Constant "∧") t) (Constant "true")) = simplify t
simplify (Apply (Constant "∀") (Lambda x s (Constant "true"))) = (Constant "true")
simplify (Apply t1 t2) = Apply (simplify t1) (simplify t2)
simplify (Lambda x s t) = Lambda x s (simplify t)
simplify t = t

--Apply simplify until it has no further effect
simp :: Term -> Term
simp t = simp' t (simplify t)
    where simp' t t'= if t==t' then t else simp t'


type Clause = (Term,([String],String))

-- given a conjunctions of implications, apply the unfold simplification
-- do not unfold variable in 'preserved'
proc :: Term -> [Variable] -> Term
proc t preserved = unpreproc (f preserved [] ks) vss
    where (ks,vss) = preproc t

unpreproc :: [Clause] -> [(Variable,Sort)] -> Term
unpreproc = foldr (\ (v,s) t -> if v `occursIn` t then aforall v s t else t) . foldl1 aand . map (\ (t,(xs,v)) ->
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


-- apply the unfold simplification to a term in the form of a list of clauses
f :: [Variable] -> [Clause] -> [Clause] -> [Clause]
f vs ks [] = ks
f vs ks1 ((body,(params,headvar)):ks2) = if headvar `elem` vs || headvar `elem` freeVars body
    then f vs ((body,(params,headvar)):ks1) ks2
    else f vs (map sub ks1) (map sub ks2)
    where sub = \(x,y) -> (subs (body,(params,headvar)) [] x, y)

-- substitute something for an instance 
subs :: Clause -> [Term] -> Term -> Term
subs (body,(params,v)) args (Variable x) = if x==v
    then if length args < length params
        then error ("too few arguments to "++x)
        else foldl (Apply) (replaceInTerm (zip params args) body) (drop (length params) args)
    else foldl (Apply) (Variable x) args
subs k args (Apply t1 t2) = subs k (subs k [] t2:args) t1
subs k args (Lambda x s t) = foldl (Apply) (Lambda x s (subs k [] t)) args
subs k args (Constant c) = foldl (Apply) (Constant c) args
