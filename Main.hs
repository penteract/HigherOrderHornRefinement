module Main where

import System.Environment
import System.IO

import Fresh(fromM)
import Parser
import Transform
import FormulaChecks
import Inference(inferProg,infer)
import DataTypes
import Data.Maybe(fromJust)
import Control.Applicative--((<*>))

runMf = fst.flip fromM 0

(<$*) :: Monad m => m a -> (a -> m b) -> m a
(<$*) xm f = do
    x<-xm
    f x
    return x

usage handle = getProgName >>= hPutStrLn handle.(\n-> unlines
    ["Usage: "++n++" [INPUT [OUTPUT]]",
     "Given a system of higher order horn clauses, output a system of first order horn clauses",
     "If the resulting clauses are satifiable, then the input was",
     "If filenames are not given, uses standard input/output",
     "",
     "OPTIONS:",
     "-h    show this message",
     "-n    don't try to read unicode",
     "-u    output in unicode"])
{-
withUTF fname mode op = withFile fname mode (\h -> do
    hSetEncoding h utf8
    op h)

openUTF fname mode = do
    h <- openFile fname mode
    hSetEncoding h utf8
    return h

readUTF fname = openUTF fname ReadMode >>= hGetContents
writeUTF fname s = withUTF fname WriteMode (flip hPutStr s)
-}

main :: IO ()
main = getArgs >>= main' []

type Options = [Char]

main' :: Options -> [String] -> IO ()
main' os _
    | 'h' `elem` os = usage stdout
main' os [] = run' os "input" (return stdin) ($stdout)
main' os (('-':ops):rest) = main' (ops++os) rest
main' os [inf] = run' os inf (openFile inf ReadMode) ($stdout)
main' os [inf,outf] = run' os inf (openFile inf ReadMode) (withFile outf WriteMode)
main' os _ = do
    hPutStrLn stderr "Error: bad arguments"
    usage stderr

hSetUTF8 :: Handle -> IO ()
hSetUTF8 = (flip hSetEncoding utf8)
makeInpUTF :: IO Handle -> IO Handle
makeInpUTF = (<$* hSetUTF8)

makeOutUTF :: ((Handle -> IO ()) -> IO ()) -> (Handle -> IO ()) -> IO ()
makeOutUTF out operation = out (\ h -> hSetUTF8 h >> operation h)


run' :: Options -> String -> IO Handle -> ((Handle -> IO ()) -> IO ()) -> IO ()
run' [] fname inh out    = run fname (makeInpUTF inh>>=hGetContents)
                                     (makeOutUTF out .flip hPutStrLn . ununicode)
run' ['n'] fname inh out = run fname (inh>>=hGetContents)
                                     (out .flip hPutStrLn . ununicode)
run' ['u'] fname inh out = run fname (makeInpUTF inh>>=hGetContents)
                                     (makeOutUTF out .flip hPutStrLn)
run' _  _ _ _            = do
    hPutStrLn stderr "Unrecognised option"
    usage stderr


run :: String -> IO String -> (String -> IO ()) -> IO ()
run fname inp out = do --io monad
    s<-inp
    case (do -- Either monad (Exceptions)
        (delta,dd,goal) <- parseFile fname s
        -- checktype dd
        prog <- return $ transformProg delta dd
        res <- runMf (do --Mfresh
          (d2,g,c1) <- inferProg delta prog
          (d3,c2,ty) <- infer g goal
          return$return (aand c1 c2))
        return $ printOut res) of
        Right a -> out a
        Left e -> hPutStrLn stderr e
