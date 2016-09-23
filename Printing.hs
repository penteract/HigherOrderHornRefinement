module Printing where
{-}
import System.Environment
import System.IO
import System.Console.GetOpt

import Fresh(fromM)
import Parser
import Transform
import FormulaChecks
import Inference(inferProg,infer)
import DataTypes
import Data.Maybe(fromJust)
import Data.List
import Control.Applicative--((<*>))
import Simplify
import Tools
-}
import DataTypes
import Data.List
import Simplify
import Parser(legiblise)
import Tools
import Transform

base :: Term -> Variable
base (Apply a b) = base a
base (Variable x) = x

smtPrint :: (DeltaEnv,Gamma,Term,Term) -> String
smtPrint (d,g,t,gt) = legiblise (unlines [
    unlines $ map smtDecFun d,
    smtTerm' t,
    --smtTerm' (pullOutAllQuantifiers True t),
    let (t,qs)=(pullOutAllQuantifiers False gt) in
        "(query {} :print-certificate true)" % [base t]
    ]) smtl smtl
smtl = [ ("and","∧"), ("=>","⇒"), ("or","∨"), ("not","¬")]

smtDecFun :: (Variable,Sort) -> String
smtDecFun (v,s) = "(declare-rel {} ({}))" % [v, intercalate " " $ map show ss]
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