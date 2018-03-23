{-
A module containing additional functions for printing.
In particular, this includes functions for producing SMT-LIB output that can be processed by Z3
-}

module HOCHC.Printing(printOut,pprint,printInd,smtPrint,smtPrint2,printEnv,printLog) where

import Data.List
import HOCHC.DataTypes
import HOCHC.Simplify
import HOCHC.Parser(legiblise)
import HOCHC.Utils
import HOCHC.Transform(vlist,slist,occursIn,split')

base :: Term -> Variable
base (Apply a b) = base a
base (Variable x) = x
base other = error ("Printing.hs, base: \n" ++ show other)

smtPrint :: ((DeltaEnv,Gamma,Term,Term),Bool) -> String
smtPrint ((d,g,t,gt),s) = legiblise (unlines [
    "(echo \"a result of unsat means that there is a model for the program clauses in which the goal clause does not hold\")",
    unlines $ map smtDecFun (d++[("goal_",Bool)]),
    smtTerm' (t `aand` aimplies gt (Variable "goal_")),
    "(query goal_"++(if s then "" else " :print-certificate true")++")"
    ]) smtl
smtl = [ ("and","∧"), ("=>","⇒"), ("or","∨"), ("not","¬")]

smtDecFun :: (Variable,Sort) -> String
smtDecFun (v,s) = "(declare-rel {} ({}))" % [v, intercalate " " $ map prnS ss]
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

smtTerm :: Term -> String
smtTerm (Apply (Apply (Constant c) t1) t2)
    | c == "≠" = "(not (= {} {}))"%[smtTerm t1, smtTerm t2]
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


-- Prints conjunctive terms on separate lines
printLong :: Term -> String
printLong (Apply (Apply (Constant "∧") t1) t2) = printLong t1 ++ '\n':printLong t2
printLong x = prnt x

--prints conjunctive terms on separate lines and indents foralls
printInd' :: Int -> [(Variable,Sort)] -> Term -> String
printInd' n vss (Apply (Constant "∀") (Lambda x s t)) = printInd' n ((x,s):vss) t
printInd' n (vs:vss) t = replicate n ' ' ++'∀':intercalate "," (map (\(v,s)->"{}:{}"%[v,prns s])(vs:vss)) ++
    "\n" ++ printInd' (n+2+2*length vss) [] t
printInd' n [] (Apply (Apply (Constant "∧") t1) t2) =
    printInd' n [] t1 ++ '\n':printInd' n [] t2
printInd' n [] x = replicate n ' ' ++ prnt x


printOut = printLong.simp.stripQuantifiers
printInd = printInd' 0 []
pprint = putStrLn.printLong.simp.stripQuantifiers



smtPrint2:: ((DeltaEnv,Gamma,Term,Term),Bool) -> String
smtPrint2 ((d,g,t,gt),s) = legiblise (unlines [
    "(set-logic HORN)",
    unlines $ map smtDecFun2 d,
    smtTerm2' (pullOutAllQuantifiers True t),
    let (t,qs)=(pullOutAllQuantifiers False gt) in
        smtTerm2' (aimplies t (Constant "false"), qs),
    "(echo \"a result of sat means that there is a model for the program clauses in which the goal clause does not hold\")",
    "(check-sat)",
    (if s then "" else "(get-model)")
    ]) smtl

smtDecFun2 :: (Variable,Sort) -> String
smtDecFun2 (v,s) = "(declare-fun {} ({}) {})" % [v, intercalate " " $ map prnS ss, prnS sb]
    where (ss,sb) = fromRight $ slist s


smtTerm2' :: (Term,[(String,Sort)]) -> String
smtTerm2' (t,[]) = "(assert {})" % [smtTerm t]
smtTerm2' (t,d) = unlines $ map (\ t -> "(assert (forall ({}) {}))" %
    [concatMap (\(x,y) -> "({} {})"%[x,prnS y]) (filter ((`occursIn` t) . fst) d), smtTerm t]) ts
    where
        ts = deand t


--logic program format - suitable for Long's defunctionalisation
printLog :: (DeltaEnv,Term,Term) -> String
printLog (d,t,g) = unlines[
    "environment",
    printEnv d,
    "program",
    unlines$ map (printLogLine d)$ deand t,
    "goal",
    show$ removeNeq g]

printLogLine :: DeltaEnv -> Term -> String
printLogLine d clause = let
    Right (body,(args,n)) = split' clause
    Just s = lookup n d in
    "{} := {};"%[n, foldr (\(v,s) b -> ("\\\\{} : {}. "%[v,prns s])++b) (show$ removeNeq body) (zip args$ fst$ fromRight$ slist s)]

printEnv :: DeltaEnv -> String
printEnv [] = ""
printEnv (("main",_):d) = printEnv d
printEnv ((v,s):d) = v++" : "++prns s++"\n"++ printEnv d

removeNeq :: Term -> Term
removeNeq (Apply (Apply (Constant "≠") a) b) = let app2 c = (Apply (Apply (Constant c) a) b) in
    aor  (app2 "<") (app2 ">")
removeNeq t = appdown removeNeq t
