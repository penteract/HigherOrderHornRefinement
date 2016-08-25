module Main where

import System.Environment
import System.IO

import Parser
import Transform
import FormulaChecks
import Inference
import DataTypes
import Data.Maybe(fromJust)

testMf = fst.flip fromM 0
snd3 = (\(a,b,c)->b)
trd = (\(a,b,c)->c)



test8 = "z = x + y ⇒ add x y z\n"++
        "n ≤ 0 ∧ r = 0 ⇒ iter f n r\n"++
        "(∃p:int. n > 0 ∧ iter f (n − 1 ) p ∧ f n p r ) ⇒ iter f n r\n"

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

usage = getProgName >>= putStr.(\n->
    "Usage: "++n++" [INPUT [OUTPUT]]"++
    "Given a system of higher order horn clauses, output a system of first order horn clauses\n"++
    "If the resulting clauses are satifiable, then the input was\n" ++
    "If filenames are not given, uses standard input/output\n"
    )

openUTF fname mode = do
    h <- openFile fname mode
    hSetEncoding h utf8
    return h

readUTF fname = openUTF fname ReadMode >>= hGetContents
writeUTF fname s = openUTF fname WriteMode >>= flip hPutStr s

main :: IO ()
main = getArgs >>=main'

main' [] = run "input" getContents putStr
main' [x]
    | x/="" && head x == '-' = usage
    | otherwise = run x (readUTF x) putStr
main' [inf,outf] = run inf (readUTF inf) (writeFile outf)
main' _ = do
    putStrLn "Error: bad arguments"
    usage



run :: String -> IO String -> (String -> IO ()) -> IO ()
run fname inp out = do --io monad
    s<-inp
    case (do -- Either monad (Exceptions)
        (delta,dd,goal) <- parseFile fname s
        -- checktype dd
        prog <- return $ transformProg delta dd
        res <- testMf (do --Mfresh
          (d2,g,c1) <- inferProg delta prog
          (d3,c2,ty) <- infer g goal
          return$return (aand c1 c2))
        return $ printLong$simp res) of
        Right a -> out$lgb a
        Left e -> hPutStr stderr e
    