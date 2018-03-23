module Main where

import System.Environment
import System.IO
import System.Console.GetOpt

import HOCHC.Fresh(runFresh,lift)
import HCParser(parseFile)
import HOCHC.Parser(ununicode)
import HOCHC.Transform
import HOCHC.FormulaChecks
import HOCHC.Inference(inferProg,infer)
import HOCHC.DataTypes

import HOCHC.ExecLib

import Data.Maybe(fromJust)
import Data.List
import Control.Applicative
import HOCHC.Simplify
import HOCHC.Utils
import HOCHC.Printing


defaultOpts' :: Opt (DeltaEnv,Gamma,Term,Term)
defaultOpts' = (defaultOpts (\((d,g,t,goalt),_)->(unlines $
  [printOut t,"","goal:",show goalt])))
    { optTermOut      = \(d,g,t,goalt)->(d,g,simp t,simp goalt)}

options :: [OptDescr (Opt (DeltaEnv,Gamma,Term,Term) -> Opt (DeltaEnv,Gamma,Term,Term))]
options = baseoptions ++
    [Option ['l'] []
        (NoArg (\opts -> opts{optTermPrint = \((d,g,t,goalt),s)->unlines $
            [printInd t,"","goal:",show goalt]}))
        "print output in a longer format"
    , Option ['n'] []
        (NoArg (\opts -> opts{
            optHandleIn=id,
            optHandleOut=id}))
        "don't try to read unicode input"
    , Option ['r'] []
        (NoArg (\opts -> opts{optTermOut = (\(d,g,t,gt)->
            let t2 = proc t (foldl1 union (freeVars gt:map (freeVarsOfTy.snd) g)) in
                (filter ((`occursIn` t2) . fst) d,g,t2,gt)) . optTermOut opts}))
        "apply the unfold reduction to output"
    , Option ['s'] []
        (NoArg (\opts -> opts{optSuppress = True}))
        "Supress printing models (for use with -x or -z)"
    , Option ['t'] []
        (NoArg (\opts -> opts{optTermPrint = (\((d,g,t,gt),s)-> unlines $ map show g++map show d++"":[optTermPrint opts ((d,g,t,gt),s)])}))
        "Output additional information about types"
    , Option ['x'] []
        (NoArg (\opts -> opts{optTermPrint = smtPrint2}))
        "Output SMT-LIB format"
    , Option ['z'] []
        (NoArg (\opts -> opts{optTermPrint = smtPrint}))
        "Output in extended SMT-LIB format for Z3"
    ]

usage = mkUsage options
  (\n-> unlines
    ["Usage: "++n++" [INPUT [OUTPUT]]",
     "Given a system of higher order horn clauses, output a system of first order horn clauses",
     "If the resulting clauses are satifiable, then the input was",
     "If filenames are not given, uses standard input/output",
     ""])


main :: IO ()
main = mkMain usage defaultOpts' options run

run :: String -> String -> Either String (DeltaEnv,Gamma,Term,Term)
run fname fcontents = runFresh (do -- Mfresh monad (fresh vars + Exceptions)
        (delta,dd',goal') <- lift $ parseFile fname fcontents
        -- checktype dd
        (goal:dd) <- mapM elim (goal':dd')
        prog <- (transformProg delta dd)
        (d2,g,c1) <- inferProg delta prog
        (d3,c2,BoolT s) <- infer g goal
        return (d2++d3,g,(aand c1 c2),s)
        )
