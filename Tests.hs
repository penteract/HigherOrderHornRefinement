module Tests where

import Parser
import DataTypes
import Transform
import FormulaChecks
import Inference
import Data.Maybe(fromJust)

test1 = "∀r:int.∀n:int.∀m:int.∀Iter:(int->int->bool)->int->int->int->bool.∀f:int->int->bool. ∃x:int. ¬(n <= 0) ∧ Iter f x (n - 1) r ∧ f m x ⇒ Iter f m n r"


test2 = "Af:int->(int->int).Eg:int->int.¬ En:int.f n = g"

test3 = "y = x + 1 ⇒ Succ x y\n"++
    "n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "(∃x:int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x )⇒ Iter f m n r\n"
test4 = "Ax:int.Ay:int.y = x + 1 ⇒ Succ x y\n"++
    "An:int.Am:int.Af:int->int->bool.n ≤ 0 ∧ r = m ⇒ Iter f m n r\n"++
    "∃x:int. ¬(n ≤ 0) ∧ Iter f x (n − 1 ) r ∧ f m x ⇒ Iter f m n r\n"
test5 = "Ax,y:int,somefunction:int->int.Ea,b:int.x=somefuntion a^y=somefunction b"


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
gamma = freshEnv delta

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

freshEnv :: DeltaEnv -> Mfresh Gamma
freshEnv = sequence . map (\(a,b)-> schemeFromRelationalSort b>>=return.(,) a)

schemeFromRelationalSort :: Sort -> Mfresh Scheme
schemeFromRelationalSort rho = sfrs rho []
sfrs :: Sort -> [Variable] -> Mfresh Scheme
sfrs Bool vs = do (t,d) <- freshRel (zip vs (repeat Int)) Bool
                  return ([d],BoolT t)
sfrs (Arrow Int rho) vs = do x <- freshVar
                             (tyvs,ty) <- sfrs rho (x:vs)
                             return (tyvs,ArrowT x IntT ty)
sfrs (Arrow t1 t2) vs = do (ds1,ty1) <- sfrs t1 [] --Need to check if [] should be vs
                           (ds2,ty2) <- sfrs t2 vs
                           return (ds1++ds2,ArrowT "_" ty1 ty2 )
sfrs _ vs = error "not relational sort"


inferProg :: DeltaEnv -> [(Variable,Term)] -> Mfresh (DeltaEnv, Gamma, Term)
inferProg d prog= do
    g <- freshEnv d
    (ds,cs,tys) <- sequence (map (infer g) ts) >>= return.unzip3
    c2s<- sequence (zipWith inferSub tys (map(snd.fromJust.flip lookup g) vs))
    return (concat ds,g,foldl1 aand (zipWith aand cs c2s))
    where (vs,ts) = unzip prog

tstEnv = [("Iter",qs "(int->int->bool)->int->int->int->bool"),
    ("Succ",qs "int->int->bool")]


    
main :: IO ()
main = putStrLn.lgb $ unlines $ map fromEither  results
    where 
        results = (map ((>>return"pass.").runp) [test1,test2,test3,test4,test5,test8] ++
            [runp test1>>=getsort.head>>return "pass."] ++
            [runp test3>>=return.unlines.map (\(s,body) ->s++":="++prnt body).checkHorn tstEnv])
    
--At the moment just checks that things parse, not actually what they parse into