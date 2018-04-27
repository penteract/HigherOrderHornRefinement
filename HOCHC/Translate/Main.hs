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



--import HOCHC.Fresh(runFresh,lift)()
--import HCParser(parseFile)
import HOCHC.Transform
--import HOCHC.FormulaChecks
import HOCHC.Inference(inferProg,infer)
import HOCHC.DataTypes

import HOCHC.ExecLib
import HOCHC.Fresh(runFresh)
import HOCHC.Parser(ununicode)
import HOCHC.Simplify
import HOCHC.Translate
import HOCHC.TypeCheck
import HOCHC.FormulaChecks
import ProgParser(parseFile)
--import Utils
import HOCHC.Printing

type HOP = (DeltaEnv,Term,Term) --higher order problem
type FOP = (DeltaEnv,Gamma,Term,Term) --first order problem
type OptTy = Opt HOP (Opt FOP Bool)

horusDefault = (defaultOpts (\((d,g,t,goalt),_)->(Right$ unlines $
  [printOut t,"","goal:",show goalt])) False)
    { optTermOut      = \(d,g,t,goalt)->(d,g,simp t,simp goalt)}

defaultOpts' :: OptTy
defaultOpts' = (defaultOpts (\((d,t,goalt),_)->(Right$ unlines$
        ["environment",printEnv d,
        "program",printOut t,"","goal",show goalt])) horusDefault)
    {
      optTermOut      = \(d,t,goalt)->(d,simp t,simp goalt)
    }


options :: [OptDescr (OptTy -> OptTy)]
options = baseoptions ++
    [ Option ['g'] ["logic"]
        (NoArg (\opts -> opts{optTermPrint = \(hop,_)-> Right$printLog hop}))
        "Output in Logic program form, for compatibility with dfhochc",
      Option ['a'] ["horus"] (NoArg (\opts ->
        opts{optTermPrint = (\(hop,horusOpts) -> runHorus hop >>= applyOpts' horusOpts)}
      )) "Perform inference (horus) on the result"
    ] ++ map modify refinementoptions
    where modify (Option ss ls (NoArg f) desc) =
           Option ss ls (NoArg (\opt -> opt{optOther = f (optOther opt)})) (desc ++ " (for use with -a)")


refinementoptions :: [OptDescr (Opt FOP Bool -> Opt FOP Bool)]
refinementoptions = [Option ['l'] ["long"]
        (NoArg (\opts -> opts{optTermPrint = \((d,g,t,goalt),s)->Right$ unlines $
            [printInd t,"","goal:",show goalt]}))
        "Print output in a longer format"
    , Option ['r'] []
        (NoArg (\opts -> opts{optTermOut = (\(d,g,t,gt)->
            let t2 = proc t (foldl1 union (freeVars gt:map (freeVarsOfTy.snd) g)) in
                (filter ((`occursIn` t2) . fst) d,g,t2,gt)) . optTermOut opts}))
        "Apply the unfold reduction to output"
    , Option ['s'] []
        (NoArg (\opts -> opts{optOther = True}))
        "Supress printing models (for use with -x or -z)"
    , Option ['t'] []
        (NoArg (\opts -> opts{optTermPrint = (\((d,g,t,gt),s)->
             (\x -> unlines $ map show g++map show d++"":[x]) <$>optTermPrint opts ((d,g,t,gt),s))}))
        "Output additional information about types"
    , Option ['x'] []
        (NoArg (\opts -> opts{optTermPrint = Right . smtPrint2}))
        "Output SMT-LIB format"
    , Option ['z'] []
        (NoArg (\opts -> opts{optTermPrint = Right . smtPrint}))
        "Output in extended SMT-LIB format for Z3"
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


runHorus :: HOP -> Either String FOP
runHorus (delta, dd', goal') = runFresh (do -- Mfresh monad (fresh vars + Exceptions)
        (goal:dd) <- mapM elim (goal':deand dd')
        prog <- (transformProg delta dd)
        (d2,g,c1) <- inferProg delta prog
        (d3,c2,BoolT s) <- infer g goal
        return (d2++d3,g,(aand c1 c2),s)
        )
