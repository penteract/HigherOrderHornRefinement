module HOCHC.ExecLib(Opt(..),mkMain,defaultOpts,baseoptions,mkUsage) where

import System.Environment
import System.IO
import System.Console.GetOpt

import HOCHC.Fresh(runStateT,lift)
import HOCHC.Parser(ununicode)
import HOCHC.Transform
import HOCHC.FormulaChecks
import HOCHC.DataTypes

import Data.Maybe(fromJust)
import Data.List
import Control.Applicative
import HOCHC.Simplify
import HOCHC.Utils
import HOCHC.Printing

data Opt t = Opt
    { optHelp         :: Bool
    , optHandleIn     :: IO Handle -> IO Handle
    , optHandleOut    :: ((Handle -> IO ()) -> IO ()) -> (Handle -> IO ()) -> IO ()
    , optTermOut      :: t -> t
    , optTermPrint    :: PrintType t
    , optStringOut    :: String -> String
    , optSuppress     :: Bool
    }

type PrintType t = (t,Bool) -> String

defaultOpts :: PrintType t -> Opt t
defaultOpts pr = Opt
    { optHelp         = False
    , optHandleIn     = makeInpUTF
    , optHandleOut    = makeOutUTF
    , optTermOut      = id
    , optTermPrint    = pr
    , optStringOut    = ununicode
    , optSuppress      = False
    }

baseoptions :: [OptDescr (Opt t -> Opt t)]
baseoptions =
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
    ]

type RunType t = String -> String -> Either String t

applyOpts :: RunType t -> Opt t -> String -> IO Handle -> ((Handle -> IO ()) -> IO ()) -> IO ()
applyOpts run opt fname inh out = do
    inp <- (optHandleIn opt inh>>=hGetContents)
    case run fname inp of
        Right res -> optHandleOut opt out $ flip hPutStrLn
            $ optStringOut opt $ (\t -> optTermPrint opt (t,optSuppress opt)) $ optTermOut opt $ res
        Left err  -> hPutStrLn stderr err

mkUsage opts fn handle = getProgName >>= hPutStrLn handle . flip usageInfo opts . fn


mkMain :: (Handle -> IO ()) -> Opt t -> [OptDescr (Opt t -> Opt t)] -> RunType t -> IO ()
mkMain usage def options' run = getArgs >>= (\(o,args,errs) -> case errs of
    (a:b) -> (hPutStrLn stderr (concat errs) >> usage stderr)
    [] -> let opts = foldl (flip ($)) def o in
        if optHelp opts then
        usage stdout else
        let app = applyOpts run opts in
            case args of
                [] -> app "input" (return stdin) ($stdout)
                [inf] -> app inf (openFile inf ReadMode) ($stdout)
                [inf,outf] -> app inf (openFile inf ReadMode) (withFile outf WriteMode)
                _ -> hPutStrLn stderr "Error: bad arguments" >> usage stderr)
    . getOpt RequireOrder options'

hSetUTF8 :: Handle -> IO ()
hSetUTF8 = (flip hSetEncoding utf8)

makeInpUTF :: IO Handle -> IO Handle
makeInpUTF hm = do
    h <- hm
    hSetUTF8 h
    return h

makeOutUTF :: ((Handle -> IO ()) -> IO ()) -> (Handle -> IO ()) -> IO ()
makeOutUTF out operation = out (\ h -> hSetUTF8 h >> operation h)
