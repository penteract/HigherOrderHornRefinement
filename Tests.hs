module Tests where

import Parser
import DataTypes
import Transform
import FormulaChecks
import Inference

tests = "∀r:int.∀n:int.∀m:int.∀Iter:(int->int->bool)->int->int->int->bool.∀f:int->int->bool. ∃x:int. ¬(n <= 0) ∧ Iter f x (n - 1) r ∧ f m x ⇒ Iter f m n r"


test2 = "Af:int->(int->int).Eg:int->int.¬ En:int.f n = g"

test3 = "y = x + 1 ⇒ Succ x y\n"++
    "n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "(∃x:int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x )⇒ Iter f m n r\n"
test4 = "Ax:int.Ay:int.y = x + 1 ⇒ Succ x y\n"++
    "An:int.Am:int.Af:int->int->bool.n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "∃x:int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x ⇒ Iter f m n r\n"
test5 = "Ax,y:int,somefunction:int->int.Ea,b:int.x=somefuntion a^y=somefunction b"
    
    
tstEnv = [("Iter",qs "(int->int->bool)->int->int->int->bool"),
    ("Succ",qs "int->int->bool")]
    
main :: IO ()
main = putStrLn.lgb $ unlines $ map fromEither  results
    where 
        results = (map ((>>return"pass.").runp) [tests,test2,test3,test4,test5] ++
            [runp tests>>=getsort.head>>return "pass."] ++
            [runp test3>>=return.unlines.map (\(s,body) ->s++":="++prnt body).checkHorn tstEnv])
    
--At the moment just checks that things parse, not actually what they parse into