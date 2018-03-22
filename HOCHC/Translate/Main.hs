module Main where

--import System.Environment
--import System.IO
import System.Console.GetOpt
--import Control.Monad.Except

import HOCHC.DataTypes
--import Data.Maybe(fromJust)
import Data.List
--import Data.Char(toLower)
import Control.Arrow--(second)


import HOCHC.ExecLib
import HOCHC.Fresh(runFresh)
import HOCHC.Parser(ununicode)
import HOCHC.Simplify
import ProgParser(parseFile)
import Translate
import TypeCheck
--import Utils
import HOCHC.Printing

defaultOpts' :: Opt (DeltaEnv,Term,Term)
defaultOpts' = (defaultOpts (\((d,t,goalt),_)->(unlines$
        ["environment",printEnv d,
        "program",printOut t,"","goal",show goalt])))
    {
      optTermOut      = \(d,t,goalt)->(d,simp t,simp goalt)
    }

--options' ::
options = baseoptions ++
    [ Option ['l'] []
        (NoArg (\opts -> opts{optTermPrint = \((d,t,goalt),_)-> printLog (d,t,goalt)}))
        "Output in Logic program form, for compatibility with dfhochc"
    ]

usage = mkUsage options (\n-> unlines
    ["Usage: "++n++" [INPUT [OUTPUT]]",
     "Given a system of higher order horn clauses, output a system of first order horn clauses",
     "If the resulting clauses are satifiable, then the input was",
     "If filenames are not given, uses standard input/output",
     ""])

main :: IO ()
main = mkMain usage defaultOpts' options run

run :: String -> String -> Either String (DeltaEnv,Term,Term)
run fname programText = do --Either Monad
        defns <- parseFile fname programText
        d' <- typeCheck defns
        let (delta',mains) = partition ((/="main").fst) d'--duplicated effort
        delta <- mapM (runKleisli$ second (Kleisli rhoify)) delta'
        (prog,goal) <- runFresh (transform (delta++mains) defns)
        return (delta,prog,goal)
