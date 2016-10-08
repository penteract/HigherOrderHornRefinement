module Printing(printOut,pprint,printInd,smtPrint,smtPrint2) where

import DataTypes
import Data.List
import Simplify
import Parser(legiblise)
import Tools
import Transform

base :: Term -> Variable
base (Apply a b) = base a

base (Variable x) = x

smtPrint :: Bool -> (DeltaEnv,Gamma,Term,Term) -> String
smtPrint isNew (d,g,t,gt) = legiblise (unlines [
    ";For use with Z3, version" ++ if isNew then "4.4.2 or later" else "4.4.1 or earlier",
    "(get-info :version)",
    "(echo \"version should be "++(if isNew then ">=4.4.2" else "<=4.4.1")++"\")",
    "(echo \"a result of unsat means that there is a model for the program clauses in which the goal clause does not hold\")",
    unlines $ map smtDecFun d,
    smtTerm' t,
    --smtTerm' (pullOutAllQuantifiers True t),
    let (t,qs)=(pullOutAllQuantifiers False gt) in
        (if isNew then "" else unlines $ map (\(x,Int) -> "(declare-var {} Int)" % [x]) qs) ++
        ("(query {} :print-certificate true)" % [if isNew then base t else '(':prnt t++")"])
    ]) smtl smtl
smtl = [ ("and","∧"), ("=>","⇒"), ("or","∨"), ("not","¬")]

smtDecFun :: (Variable,Sort) -> String
smtDecFun (v,s) = "(declare-rel {} ({}))" % [v, intercalate " " $ map prns ss]
    where (ss,Bool) = fromRight $ slist s

smtTerm' :: Term -> String
smtTerm' t = unlines $ map (\(x,Int) -> "(declare-var {} Int)" % [x]) vss ++
    map (\ t -> "(rule {})" % [smtTerm t]) ts
    where
        (t',vss) = pullOutAllQuantifiers True t
        ts = deand t'

deand :: Term -> [Term]
deand (Apply (Apply (Constant "∧") t1) t2) = deand t1 ++ deand t2
deand t = [t]

pullOutAllQuantifiers :: Bool -> Term -> (Term,[(String,Sort)])
pullOutAllQuantifiers b (Apply (Apply (Constant c) t1) t2)
    | c `elem` ["⇒","∨","∧"] = (Apply (Apply (Constant c) t1') t2', vs1 `union` vs2)
        where (t1',vs1) = pullOutAllQuantifiers (b `xor` (c=="⇒")) t1
              (t2',vs2) = pullOutAllQuantifiers b t2
pullOutAllQuantifiers b (Apply (Constant "¬") t) = ((Apply (Constant "¬") t'),vs)
    where (t',vs) = pullOutAllQuantifiers (not b) t
pullOutAllQuantifiers True (Apply (Constant "∀") t) = case t of
        (Lambda x ty body) -> fmap ((x,ty):) $ pullOutAllQuantifiers True body
        _ -> error "bad quantifier"
pullOutAllQuantifiers False (Apply (Constant "∀") t) = case t of
        _ -> error "bad quantifier"
pullOutAllQuantifiers False (Apply (Constant "∃") t) = case t of
        (Lambda x ty body) -> fmap ((x,ty):) $ pullOutAllQuantifiers False body
        _ -> error "bad quantifier"
pullOutAllQuantifiers True (Apply (Constant "∃") t) = case t of
        _ -> error "bad quantifier"
pullOutAllQuantifiers b t = (t,[])


smtTerm :: Term -> String
smtTerm (Apply (Apply (Constant c) t1) t2)
    | c `elem` binaryOps = "({} {} {})"%[c, smtTerm t1, smtTerm t2]
smtTerm (Apply (Constant c) t)
    | c `elem` logicalUnary = "({} {})"%[c, smtTerm t]
    | c `elem` logicalQuantifiers = case (c,t) of
        ("∀",(Lambda x Int body)) -> "(forall (({} Int))\n  {})"%[x,smtTerm body]
        _ -> error "bad quantifier"
smtTerm (Lambda a s body)  = error "unquantified lambda"
smtTerm (Variable v)  = v
smtTerm (Constant c)  = c
smtTerm (Apply a b)  = "({} {})"% [smtApp a,smtTerm b]

smtApp (Apply a b) = "{} {}"% [smtApp a,smtTerm b]
smtApp x = smtTerm x


--prints conjunctive terms on separate lines and indents foralls
printInd' :: Int -> [(Variable,Sort)] -> Term -> String
printInd' n vss (Apply (Constant "∀") (Lambda x s t)) = printInd' n ((x,s):vss) t
printInd' n (vs:vss) t = replicate n ' ' ++'∀':intercalate "," (map (\(v,s)->"{}:{}"%[v,show s])(vs:vss)) ++
    "\n" ++ printInd' (n+2+2*length vss) [] t
printInd' n [] (Apply (Apply (Constant "∧") t1) t2) =
    printInd' n [] t1 ++ '\n':printInd' n [] t2
printInd' n [] x = replicate n ' ' ++ prnt x


printOut = printLong.simp.stripQuantifiers
printInd = printInd' 0 []
pprint = putStrLn.printLong.simp.stripQuantifiers





smtPrint2:: (DeltaEnv,Gamma,Term,Term) -> String
smtPrint2 (d,g,t,gt) = legiblise (unlines [
    "(set-logic HORN)",
    unlines $ map smtDecFun2 d,
    smtTerm2' (pullOutAllQuantifiers True t),
    let (t,qs)=(pullOutAllQuantifiers False gt) in
        smtTerm2' (aimplies t (Constant "false"), qs),
    "(echo \"a result of sat means that there is a model for the program clauses in which the goal clause does not hold\")",
    "(check-sat)",
    "(get-model)"
    ]) smtl smtl

smtDecFun2 :: (Variable,Sort) -> String
smtDecFun2 (v,s) = "(declare-fun {} ({}) {})" % [v, intercalate " " $ map show ss, show sb]
    where (ss,sb) = fromRight $ slist s

        
smtTerm2' :: (Term,[(String,Sort)]) -> String
smtTerm2' (t,[]) = "(assert {})" % [smtTerm t]
smtTerm2' (t,d) = unlines $ map (\ t -> "(assert (forall ({}) {}))" %
    [concatMap (\(x,y) -> "({} {})"%[x,prns y]) (filter ((`occursIn` t) . fst) d), smtTerm t]) ts
    where
        ts = deand t
