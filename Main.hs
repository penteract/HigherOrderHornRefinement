module Main where

import System.Environment
import System.IO
import System.Console.GetOpt

import Fresh(fromM,ret)
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
import Printing


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
      [printOut t,"","goal:",show goalt])--printInd
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
    , Option ['l'] []
        (NoArg (\opts -> opts{optTermPrint = \(d,g,t,goalt)->unlines $
            [printInd t,"","goal:",show goalt]}))
        "print output in a longer format"
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
        (NoArg (\opts -> opts{optTermPrint = (\(d,g,t,gt)-> unlines $ map show g++map show d++"":[optTermPrint opts (d,g,t,gt)])}))
        "Output additional information about types"
    , Option ['x'] []
        (NoArg (\opts -> opts{optTermPrint = smtPrint2}))
        "Output SMT-LIB format"
    , Option ['y'] []
        (NoArg (\opts -> opts{optTermPrint = smtPrint False}))
        "Output in extended SMT-LIB format for Z3 (4.4.1 or earlier)"
    , Option ['z'] []
        (NoArg (\opts -> opts{optTermPrint = smtPrint True}))
        "Output in extended SMT-LIB format for Z3 (4.4.2 or later)"
    ]

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
    case fromM (do -- Mfresh monad (fresh vars + Exceptions)
        (delta,dd',goal') <- ret $ parseFile fname s
        -- checktype dd
        (goal:dd) <- mapM elim (goal':dd')
        prog <- (transformProg delta dd)
        (d2,g,c1) <- inferProg delta prog
        (d3,c2,BoolT s) <- infer g goal
        return (d2++d3,g,(aand c1 c2),s)
        ) 0 of
        Right (a,n) -> out a
        Left e -> hPutStrLn stderr e
