module Tests where

import Parser
import DataTypes
import Transform
import FormulaChecks
import Inference
import Fresh
import Data.Maybe(fromJust)
import Data.Functor

test1 = "∀r:int.∀n:int.∀m:int.∀Iter:(int->int->bool)->int->int->int->bool.∀f:int->int->bool. ∃x:int. ¬(n <= 0) ∧ Iter f x (n - 1) r ∧ f m x ⇒ Iter f m n r"


test2 = "A f:int->(int->int).E g:int->int.¬ E n:int.f n = g"

test3 = "y = x + 1 ⇒ Succ x y\n"++
    "n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "(∃x:int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x )⇒ Iter f m n r\n"
test4 = "A x:int.A y:int.y = x + 1 ⇒ Succ x y\n"++
    "A n:int.A m:int.A f:int->int->bool.n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "∃x:int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x ⇒ Iter f m n r\n"
test5 = "A x,y:int,somefunction:int->int.E a,b:int.x=somefuntion a^y=somefunction b"


test6 = qp "n<=0^r=0"
gamma6 = [("n",([],IntT)),("r",([],IntT))]

testMf = fst.flip fromM 0
snd3 = (\(a,b,c)->b)
trd = (\(a,b,c)->c)
test = testMf$infer gamma6 test6

t1 = testMf$infer gamma6 test6


delta = [
    ("add",qs"int->int->int->bool"),--lower case add for forall safety
    ("iter",qs"(int->int->int->bool)->int->int->bool")]
gamma ::Mfresh Gamma
gamma = fst <$> freshEnv delta

test7 = "(∃x:int. ¬(n ≤ 0) ∧ iter f (n − 1 ) x ∧ f n x r ) ⇒ iter f n r"
test7' = "λf:int->int->int->bool.λn:int.λr:int.∃x:int.¬n<=0∧iter f (n-1) x∧f n x r"
t7 = qp test7
t7'= qp test7'
testing7 =  testMf (do 
    g <- gamma
    infer g (snd$ transform (flatenv g) t7))
testing7' =  testMf (do 
    g <- gamma
    infer g (qp test7'))


test8 = "z = x + y ⇒ add x y z\n"++
        "n ≤ 0 ∧ r = 0 ⇒ iter f n r\n"++
        "(∃p:int. n > 0 ∧ iter f (n − 1 ) p ∧ f n p r ) ⇒ iter f n r\n"

prog8 = transformProg delta (fromRight$runp test8)
t8 = testMf (do
    g <- gamma
    infer g (snd.head$tail prog8))

t8p = let (d,g,t) = testMf $ inferProg delta prog8 in
          do
              pprint t
              putStrLn ""
              sequence (map (putStrLn.show) d)
              putStrLn ""
              sequence (map (putStrLn.show) g)
              return ()

test8Goal = "∀nr. iter add n r ⇒ n ≤ r"

tstEnv = [("Iter",qs "(int->int->bool)->int->int->int->bool"),
    ("Succ",qs "int->int->bool")]

test9 = unlines [
    "environment",
    "add : int->int->int->bool",
    "iter:(int->int->int->bool)->int->int->bool;",
    "",
    "program",
    "z = x + y ⇒ add x y z",
    "n ≤ 0 ∧ r = 0 ⇒ iter f n r",
    "( ∃ p : int. n > 0 ∧ iter f (n − 1 ) p ∧ f n p r ) ⇒ iter f n r;",
    "",
    "goal",
    "E n,r:int. iter add n r ^ n > r"]
    
main :: IO ()
main = putStrLn.ununicode $ unlines $ map fromEither  results
    where 
        results = (map ((>>return"pass.").runp) [test1,test2,test3,test4,test5,test8] ++
            [runp test1>>=getsort.head>>return "pass."] ++
            [runp test3>>=return.unlines.map (\(s,body) ->s++":="++prnt body).checkHorn tstEnv])
    
--At the moment just checks that things parse, not actually what they parse into