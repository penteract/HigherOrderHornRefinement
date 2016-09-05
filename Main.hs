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
    {-map show d++[]:-}map show g++[]:[printOut t]++[]:"goal:":[show goalt])--printInd 0 []
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
        (NoArg (\opts -> opts{optTermOut = (\(d,g,t,gt)->(d,g,
                  flip proc (foldl1 union (freeVars gt:map (freeVarsOfTy.snd.snd) g)) t
                  ,gt)) . optTermOut opts}))
        "apply the unfold reduction to output"
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
