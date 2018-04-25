module HOCHC.ExecLib(Opt(..),mkMain,defaultOpts,baseoptions,mkUsage,applyOpts') where

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

data Opt t d = Opt
    { optHelp         :: Bool
    , optHandleIn     :: IO Handle -> IO Handle
    , optHandleOut    :: ((Handle -> IO ()) -> IO ()) -> (Handle -> IO ()) -> IO ()
    , optTermOut      :: t -> t
    , optTermPrint    :: (t,d)-> Either String String
    , optStringOut    :: String -> String
    , optOther        :: d
    }


defaultOpts :: ((t,d)-> Either String String) -> d -> Opt t d
defaultOpts pr other = Opt
    { optHelp         = False
    , optHandleIn     = makeInpUTF
    , optHandleOut    = makeOutUTF
    , optTermOut      = id
    , optTermPrint    = pr
    , optStringOut    = ununicode
    , optOther        = other
    }

baseoptions :: [OptDescr (Opt t d -> Opt t d)]
baseoptions =
    [ Option ['h'] ["help"]
        (NoArg (\opts -> opts{optHelp=True}))
        "Show this message"
    , Option ['u'] []
        (NoArg (\opts -> opts{optStringOut=id}))
        "Output using unicode characters"
    {-, Option ['n'] []
        (NoArg (\opts -> opts{
            optHandleIn=id,
            optHandleOut=id}))
        "don't try to read unicode input"-}
    ]

type RunType t = String -> String -> Either String t

applyOpts :: RunType t -> Opt t d -> String -> IO Handle -> ((Handle -> IO ()) -> IO ()) -> IO ()
applyOpts run opt fname inh out = do
    inp <- (optHandleIn opt inh>>=hGetContents)
    case run fname inp >>= applyOpts' opt  of
        Right str -> optHandleOut opt out $ flip hPutStrLn str
        Left err  -> hPutStrLn stderr (optStringOut opt $ err)

applyOpts' :: Opt t d -> t -> Either String String
applyOpts' opt res = optStringOut opt <$>  optTermPrint opt (optTermOut opt res,optOther opt)

mkUsage opts fn handle = getProgName >>= hPutStrLn handle . flip usageInfo opts . fn


mkMain :: (Handle -> IO ()) -> Opt t d -> [OptDescr (Opt t d -> Opt t d)] -> RunType t -> IO ()
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
