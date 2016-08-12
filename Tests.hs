module Tests where

import Parser
import DataTypes
import Transform

tests = "∀r:Int.∀n:Int.∀m:Int.∀Iter:(Int->Int->Bool)->Int->Int->Int->Bool.∀f:Int->Int->Bool. ∃x:Int. ¬(n <= 0) ∧ Iter f x (n - 1) r ∧ f m x ⇒ Iter f m n r"


test2 = "Af:Int->(Int->Int).Eg:Int->Int.¬ En:Int.f n = g"

test3 = "y = x + 1 ⇒ Succ x y\n"++
    "n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "(∃x:Int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x )⇒ Iter f m n r\n"
test4 = "Ax:Int.Ay:Int.y = x + 1 ⇒ Succ x y\n"++
    "An:Int.Am:Int.Af:Int->Int->Bool.n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "∃x:Int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x ⇒ Iter f m n r\n"
    
    
tstEnv = [("Iter",qs "(Int->Int->Bool)->Int->Int->Int->Bool"),
    ("Succ",qs "Int->Int->Bool")]
    
main :: IO ()
main = putStrLn $ unlines $ map fromEither  results
    where 
        results = (map ((>>=return.const"pass.").runp) [tests,test2,test3,test4] ++
            [runp tests>>=getsort.head>>=return.const "pass."] ++
            [runp test3>>=return.unlines.map (\(s,body) ->s++":="++prnt body).checkHorn tstEnv])
    
--At the moment just checks that things parse, not actually what they parse into