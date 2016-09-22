module Main where

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

runMf = fst.flip fromM 0

(<$*) :: Monad m => m a -> (a -> m b) -> m a
(<$*) xm f = do
    x<-xm
    f x
    return x

data Opt = Opt
    { optHelp         :: Bool
    , optHandleIn     :: IO Handle -> IO Handle
    , optHandleOut    :: ((Handle -> IO ()) -> IO ()) -> (Handle -> IO ()) -> IO ()
    , optTermOut      :: (DeltaEnv,Gamma,Term,Term) -> (DeltaEnv,Gamma,Term,Term)
    , optTermPrint    :: (DeltaEnv,Gamma,Term,Term) -> String
    , optStringOut    :: String -> String
    }

defaultOpts = Opt
    { optHelp         = False
    , optHandleIn     = makeInpUTF
    , optHandleOut    = makeOutUTF
    , optTermOut      = \(d,g,t,goalt)->(d,g,simp t,simp goalt)
    , optTermPrint    = \(d,g,t,goalt)->(unlines $
      [printOut t,"","goal:",show goalt])--printInd 0 []
    , optStringOut    = ununicode
    }

options :: [OptDescr (Opt -> Opt)]
options =
    [ Option ['h'] ["help"]
        (NoArg (\opts -> opts{optHelp=True}))
        "show this message"
    , Option ['u'] []
        (NoArg (\opts -> opts{optStringOut=id}))
        "output in unicode"
    , Option ['n'] []
        (NoArg (\opts -> opts{
            optHandleIn=id,
            optHandleOut=id}))
        "don't try to read unicode input"
    , Option ['r'] []
        (NoArg (\opts -> opts{optTermOut = (\(d,g,t,gt)->
            let t2 = proc t (foldl1 union (freeVars gt:map (freeVarsOfTy.snd.snd) g)) in
                (filter ((`occursIn` t2) . fst) d,g,t2,gt)) . optTermOut opts}))
        "apply the unfold reduction to output"
    , Option ['t'] []
        (NoArg (\opts -> opts{optTermPrint = (\(d,g,t,gt)-> unlines $ map show d++"":[optTermPrint opts (d,g,t,gt)])}))
        "Output additional information about types"
    , Option ['z'] []
        (NoArg (\opts -> opts{optTermPrint = smtPrint}))
        "Output in SMT-LIB format for Z3 (under construction)"
    ]

smtPrint:: (DeltaEnv,Gamma,Term,Term) -> String
smtPrint (d,g,t,gt) = legiblise (unlines [
    unlines $ map smtDecFun d,
    smtTerm' (pullOutAllQuantifiers True t),
    let (t,qs)=(pullOutAllQuantifiers False gt) in
        smtTerm' (Apply (Constant "¬") t, qs),
    "(check-sat)"
    ]) smtl smtl
smtl = [ ("and","∧"), ("=>","⇒"), ("or","∨"), ("not","¬")]

smtDecFun :: (Variable,Sort) -> String
smtDecFun (v,s) = "(declare-fun {} ({}) {})" % [v, intercalate " " $ map show ss, show sb]
    where (ss,sb) = fromRight $ slist s

pullOutAllQuantifiers :: Bool -> Term -> (Term,[(String,Sort)])
pullOutAllQuantifiers b (Apply (Apply (Constant c) t1) t2)
    | c `elem` ["⇒","∨","∧"] = (Apply (Apply (Constant c) t1') t2', vs1 `union` vs2)
    -- | otherwise = error (c++show t1 ++ show t2)
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

smtTerm' :: (Term,[(String,Sort)]) -> String
smtTerm' (t,[]) = "(assert {})" % [smtTerm t]
smtTerm' (t,d) = "(assert (forall ({}) {}))" %
    [concatMap (\(x,y) -> "({} {})"%[x,show y]) d, smtTerm t]

smtTerm :: Term -> String
smtTerm (Apply (Apply (Constant c) t1) t2)
    | c `elem` binaryOps = "({} {} {})"%[c, smtTerm t1, smtTerm t2]
smtTerm (Apply (Constant c) t)
    | c `elem` logicalUnary = "({} {})"%[c, smtTerm t]
    | c `elem` logicalQuantifiers = case (c,t) of
        ("∀",(Lambda x Int body)) -> "(forall (({} Int))\n  {})"%[x,smtTerm body]
        --("∃",(Lambda x Int body)) -> "(therex (({} Int))  {})"%[x,smtTerm body]--
        _ -> error "bad quantifier"
smtTerm (Lambda a s body)  = error "unquantified lambda"
smtTerm (Variable v)  = v
smtTerm (Constant c)  = c
smtTerm (Apply a b)  = "({} {})"% [smtApp a,smtTerm b]

smtApp (Apply a b) = "{} {}"% [smtApp a,smtTerm b]
smtApp x = smtTerm x

applyOpts :: Opt -> String -> IO Handle -> ((Handle -> IO ()) -> IO ()) -> IO ()
applyOpts opt fname inh out = run fname
    (optHandleIn opt inh>>=hGetContents)
    (optHandleOut opt out . flip hPutStrLn
        . optStringOut opt . optTermPrint opt . optTermOut opt)

usage handle = getProgName >>= hPutStrLn handle . flip usageInfo options .
  (\n-> unlines
    ["Usage: "++n++" [INPUT [OUTPUT]]",
     "Given a system of higher order horn clauses, output a system of first order horn clauses",
     "If the resulting clauses are satifiable, then the input was",
     "If filenames are not given, uses standard input/output",
     ""])



main :: IO ()
main = getArgs >>= (\(o,args,errs) -> case errs of
    (a:b) -> (hPutStrLn stderr (concat errs) >> usage stderr)
    [] -> let opts = foldl (flip ($)) defaultOpts o in
        if optHelp opts then
        usage stdout else
        case args of
            [] -> applyOpts opts "input" (return stdin) ($stdout)
            [inf] -> applyOpts opts inf (openFile inf ReadMode) ($stdout)
            [inf,outf] -> applyOpts opts inf (openFile inf ReadMode) (withFile outf WriteMode)
            _ -> hPutStrLn stderr "Error: bad arguments" >> usage stderr)
    . getOpt RequireOrder options

hSetUTF8 :: Handle -> IO ()
hSetUTF8 = (flip hSetEncoding utf8)

makeInpUTF :: IO Handle -> IO Handle
makeInpUTF = (<$* hSetUTF8)

makeOutUTF :: ((Handle -> IO ()) -> IO ()) -> (Handle -> IO ()) -> IO ()
makeOutUTF out operation = out (\ h -> hSetUTF8 h >> operation h)

run :: String -> IO String -> ((DeltaEnv,Gamma,Term,Term) -> IO ()) -> IO ()
run fname inp out = do --io monad
    s<-inp
    case (do -- Either monad (Exceptions)
        (delta,dd,goal) <- parseFile fname s
        -- checktype dd
        prog <- transformProg delta dd
        runMf (do --Mfresh
          (d2,g,c1) <- inferProg delta prog
          (d3,c2,BoolT s) <- infer g goal
          return $ return (d2++d3,g,(aand c1 c2),s))
        ) of
        Right a -> out a
        Left e -> hPutStrLn stderr e
