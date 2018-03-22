module Main where

import System.Environment
import System.IO
import System.Console.GetOpt
--import Control.Monad.Except

import HOCHC.DataTypes
--import Data.Maybe(fromJust)
import Data.List
--import Data.Char(toLower)
import Control.Arrow--(second)


import HOCHC.Fresh(runFresh)
import HOCHC.Parser(ununicode)
import HOCHC.Simplify
import ProgParser(parseFile)
import Translate
import TypeCheck
--import Utils
import HOCHC.Printing

data Opt = Opt
    { optHelp         :: Bool
    , optHandleIn     :: IO Handle -> IO Handle
    , optHandleOut    :: ((Handle -> IO ()) -> IO ()) -> (Handle -> IO ()) -> IO ()
    , optTermOut      :: (DeltaEnv,Term,Term) -> (DeltaEnv,Term,Term)
    , optTermPrint    :: (DeltaEnv,Term,Term,Bool) -> String
    , optStringOut    :: String -> String
    , optSuppress     :: Bool
    }

defaultOpts = Opt
    { optHelp         = False
    , optHandleIn     = makeInpUTF
    , optHandleOut    = makeOutUTF
    , optTermOut      = \(d,t,goalt)->(d,simp t,simp goalt)
    , optTermPrint    = \(d,t,goalt,_)->(unlines $
        ["environment",printEnv d,
        "program",printOut t,"","goal",show goalt])--printInd
    , optStringOut    = ununicode
    , optSuppress      = False
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
    {-, Option ['l'] []
        (NoArg (\opts -> opts{optTermPrint = \(d,t,goalt,_)->unlines $
            ["environment",printEnv d,"program",printInd t,"","goal",show goalt]}))
        "print output in a longer format"-}
    , Option ['l'] []
        (NoArg (\opts -> opts{optTermPrint = \(d,t,goalt,_)-> printLog (d,t,goalt)}))
        "Output in Logic program form, for compatibility with dfhochc"
    {-, Option ['r'] []
        (NoArg (\opts -> opts{optTermOut = (\(d,g,t,gt)->
            let t2 = proc t (foldl1 union (freeVars gt:map (freeVarsOfTy.snd) g)) in
                (filter ((`occursIn` t2) . fst) d,g,t2,gt)) . optTermOut opts}))
        "apply the unfold reduction to output"-}
    {-, Option ['s'] []
        (NoArg (\opts -> opts{optSuppress = True}))
        "Supress printing models (for use with -x or -z)"
    , Option ['t'] []
        (NoArg (\opts -> opts{optTermPrint = (\(d,g,t,gt,s)-> unlines $ map show g++map show d++"":[optTermPrint opts (d,g,t,gt,s)])}))
        "Output additional information about types"
    , Option ['x'] []
        (NoArg (\opts -> opts{optTermPrint = smtPrint2}))
        "Output SMT-LIB format"
    , Option ['z'] []
        (NoArg (\opts -> opts{optTermPrint = smtPrint}))
        "Output in extended SMT-LIB format for Z3"-}
    ]

applyOpts :: Opt -> String -> IO Handle -> ((Handle -> IO ()) -> IO ()) -> IO ()
applyOpts opt fname inh out = run fname
    (optHandleIn opt inh>>=hGetContents)
    (optHandleOut opt out . flip hPutStrLn
        . optStringOut opt . (\(a,c,d) -> optTermPrint opt (a,c,d,optSuppress opt)) . optTermOut opt)

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
makeInpUTF hm = do
    h <- hm
    hSetUTF8 h
    return h

makeOutUTF :: ((Handle -> IO ()) -> IO ()) -> (Handle -> IO ()) -> IO ()
makeOutUTF out operation = out (\ h -> hSetUTF8 h >> operation h)

run :: String -> IO String -> ((DeltaEnv,Term,Term) -> IO ()) -> IO ()
run fname inp out = do -- IO Monad
    programText <- inp
    case (do --Either Monad
        defns <- parseFile fname programText
        d' <- typeCheck defns
        let (delta',mains) = partition ((/="main").fst) d'--duplicated effort
        delta <- mapM (runKleisli$ second (Kleisli rhoify)) delta'
        (prog,goal) <- runFresh (transform (delta++mains) defns)
        return (delta,prog,goal)
        ) of
        Right a -> out a
        Left e -> hPutStrLn stderr e

{-
run :: String -> IO String -> ((DeltaEnv,Gamma,Term,Term) -> IO ()) -> IO ()
run fname inp out = do --IO monad
    s<-inp
    case runStateT (do -- Mfresh monad (fresh vars + Exceptions)
        (delta,dd',goal') <- lift $ parseFile fname s

        ) 0 of
        Right (a,n) -> out a
        Left e -> hPutStrLn stderr e
-}
