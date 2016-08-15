module Tests where

import Parser
import DataTypes
import Transform
import FormulaChecks

tests = "∀r:Int.∀n:Int.∀m:Int.∀Iter:(Int->Int->Bool)->Int->Int->Int->Bool.∀f:Int->Int->Bool. ∃x:Int. ¬(n <= 0) ∧ Iter f x (n - 1) r ∧ f m x ⇒ Iter f m n r"


test2 = "Af:Int->(Int->Int).Eg:Int->Int.¬ En:Int.f n = g"

test3 = "y = x + 1 ⇒ Succ x y\n"++
    "n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "(∃x:Int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x )⇒ Iter f m n r\n"
test4 = "Ax:Int.Ay:Int.y = x + 1 ⇒ Succ x y\n"++
    "An:Int.Am:Int.Af:Int->Int->Bool.n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "∃x:Int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x ⇒ Iter f m n r\n"
test5 = "Ax,y:Int,somefunction:Int->Int.Ea,b:Int.x=somefuntion a^y=somefunction b"
    
    
tstEnv = [("Iter",qs "(Int->Int->Bool)->Int->Int->Int->Bool"),
    ("Succ",qs "Int->Int->Bool")]
    
main :: IO ()
main = putStrLn.lgb $ unlines $ map fromEither  results
    where 
        results = (map ((>>return"pass.").runp) [tests,test2,test3,test4,test5] ++
            [runp tests>>=getsort.head>>return "pass."] ++
            [runp test3>>=return.unlines.map (\(s,body) ->s++":="++prnt body).checkHorn tstEnv])
    
--At the moment just checks that things parse, not actually what they parse into