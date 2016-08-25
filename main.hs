module Main where

import System.Environment
import System.IO

import Parser
import Transform
import FormulaChecks
import Inference
import DataTypes
import Data.Maybe(fromJust)
import Control.Applicative--((<*>))

testMf = fst.flip fromM 0
snd3 = (\(a,b,c)->b)
trd = (\(a,b,c)->c)

(<$*) :: Monad m => m a -> (a -> m b) -> m a
(<$*) xm f = do
    x<-xm
    f x
    return x

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

usage = getProgName >>= hPutStrLn stderr.(\n-> unlines
    ["Usage: "++n++" [INPUT [OUTPUT]]",
     "Given a system of higher order horn clauses, output a system of first order horn clauses",
     "If the resulting clauses are satifiable, then the input was",
     "If filenames are not given, uses standard input/output",
     "",
     "OPTIONS:",
     "-h    show this message",
     "-n    don't try to read unicode",
     "-u    output in unicode"])

withUTF fname mode op = withFile fname mode (\h -> do
    hSetEncoding h utf8
    op h)

openUTF fname mode = do
    h <- openFile fname mode
    hSetEncoding h utf8
    return h

readUTF fname = openUTF fname ReadMode >>= hGetContents
writeUTF fname s = withUTF fname WriteMode (flip hPutStr s)

main :: IO ()
main = getArgs >>= main' []

type Options = [Char]

main' :: Options -> [String] -> IO ()
main' os _
    | 'h' `elem` os = usage
main' os [] = run' os "input" (return stdin) ($stdout)
main' os (('-':ops):rest) = main' (ops++os) rest
main' os [inf] = run' os inf (openFile inf ReadMode) ($stdout)
main' os [inf,outf] = run' os inf (openFile inf ReadMode) (withFile outf WriteMode)
main' os _ = do
    hPutStrLn stderr "Error: bad arguments"
    usage

hSetUTF8 :: Handle -> IO ()
hSetUTF8 = (flip hSetEncoding utf8)
makeInpUTF :: IO Handle -> IO Handle
makeInpUTF = (<$* hSetUTF8)

makeOutUTF :: ((Handle -> IO ()) -> IO ()) -> (Handle -> IO ()) -> IO ()
makeOutUTF out operation = out ((>>).hSetUTF8 <*> operation)


run' :: Options -> String -> IO Handle -> ((Handle -> IO ()) -> IO ()) -> IO ()
run' [] fname inh out    = run fname
                               (makeInpUTF inh>>=hGetContents)
                               (makeOutUTF out .flip hPutStr . lgb)
run' ['n'] fname inh out = run fname
                               (inh>>=hGetContents)
                               (out .flip hPutStr . lgb)
run' ['u'] fname inh out = run fname
                               (inh>>=hGetContents)
                               (out .flip hPutStr)
run' _  _ _ _            = do
    hPutStrLn stderr "Unrecognised option"
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
        return $ printLong$ simp res) of
        Right a -> out a
        Left e -> hPutStrLn stderr e
