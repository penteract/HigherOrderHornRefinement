{-# LANGUAGE FlexibleInstances,FlexibleContexts #-}{-
Functions for transforming a higher-order constrained Horn clause problem into a logic safety problem
See Section 3.2.
-}

module HOCHC.Translate(transformLine,transform,rhoify)
    where

import HOCHC.Fresh(Mfresh)
import qualified HOCHC.Fresh as Fresh
import HOCHC.DataTypes
import HOCHC.Utils
--import FormulaChecks(typeCheck)
import Data.Maybe(fromJust)
import Control.Monad(liftM,liftM2)
import Control.Monad.Except(throwError,lift,MonadError)
import Data.Semigroup
-- import Data.Bifunctor
import Data.List(partition)

import Control.Monad.Reader
import Control.Monad.Writer hiding ((<>))

--import Data.Monoid (Monoid, mempty, mappend, (<>))
--newtype ModTerm = MT (Term -> Term)
--instance Monoid ModTerm

instance {-# OVERLAPPING #-} Semigroup (a -> a) where
    f <> g = f . g

instance {-# OVERLAPPING #-} Monoid (a -> a) where
    mempty = id
    mappend = (<>)


-- Fresh variables, a frozen environment, and a modifier that keeps track of
-- things to do once we get back to somewhere that knows it has type o
type Tfresh = ReaderT DeltaEnv (WriterT (Term -> Term) Mfresh)

freshVar = lift$ lift$ Fresh.freshVarx "y"

--given a monadic computation of a term, use the written modifier  then erase it
extractTerm :: Tfresh Term -> Tfresh Term
extractTerm = (censor$ const id) . (uncurry (flip id) <$>) . listen --why do I hate people that read my code? particularly as it's mostly me

transform :: DeltaEnv -> [Definition] -> Mfresh (Term,Term)
transform env defns =
    let (mains,fns) = partition (\(n,_,_)->n=="main") defns in--TODO: change to give error message
    case mains of
        [main] -> errorPart "(should not see this if typechecked beforehand) Transformation" $ do
            prog <- foldl1 aand <$> mapM (transformLine env) fns
            goal <- (transformGoal env main)
            return (prog,goal)
        _ -> throwError "There must be exactly one main function"

transformLine :: DeltaEnv -> Definition -> Mfresh Term
transformLine env (n, args, body) = do
    s <- lookup n env ? "this is a problem"
    let env' = zip args (fst$ slist s) ++ env
    v<- Fresh.freshVarx "y"
    (t,fn) <- runWriterT (runReaderT (transformInt body v) (env'))
    return$ aimplies (fn t) (foldl Apply (Variable n) (map Variable $ args++[v]))

--need to negate it
transformGoal :: DeltaEnv -> Definition -> Mfresh Term
transformGoal env (n,args,body) = do
    s <- lookup n env ? "this is a problem"
    let ss = fst$ slist s
    check (all (==Int) ss) "bad main type"
    let env' = zip args (fst$ slist s) ++ env
    body' <- neg body
    (t,fn) <- runWriterT (runReaderT (transformBool body') (env'))
    return$ (foldl (flip$ uncurry aexists) (fn t)  (zip args (repeat Int)))

getSort :: Term -> Tfresh Sort
getSort (Variable v) = do
     ms <- reader (lookup v)
     maybe (throwError ("Can't find sort of variable "++v)) return ms
getSort (Apply s t) = do --does not check t and assumes it just works
    sigma <- getSort s--unsafe
    case sigma of
        (Arrow a b) -> return b
        _ -> throwError "Bad sort"
getSort (Constant c) =do
    if isIntegerConstant c
    then return Int
    else maybe (throwError ("Can't find sort of constant "++c)) return (lookup c ilaEnv)
getSort (If c t e) = getSort t --again does not typecheck


varSort :: Variable -> Tfresh Sort
varSort v = do
     ms <- reader (lookup v)
     maybe (throwError ("Can't find sort of variable "++v)) return ms
--transforms a term where the head is a variable into an atom or part of an atom
-- (for it to be an atom, it would really need integer sort to begin with)
{-toAtom':: Term -> Tfresh Term
toAtom' t = do
    s <- getSort t
    toAtom s t-}

--note the assumption that constants are applied

--given a term and the expected sort, coerce the sort to match the term, then
toAtom :: Sort -> Term -> Tfresh Term
toAtom Bool _ =
    throwError "expecting non-relational sort"
toAtom Int t@(Variable v) = return t
toAtom Int t = do --need to be more careful here - whether it really is an int and whether it really needs an int is hard to determine. (assume it always really needs an int)
    v <- freshVar
    e <- transformInt t v
    tell (aexists v Int . aand e)
    return (Variable v)
--toAtom (Arrow Int Bool) t = do
--    v <- freshVar
--    e <- transformInt t v --real recursion problems (I think they're gone now)
--    tell (aexists v Int . aand e)
--    return (Variable v)
toAtom ty@(Arrow a b) t= do --(Apply s t) = do
    let (args,h) = tlist t
    case h of
        (Variable f) -> do
            fsort <- varSort f
            let (sorts,Bool) = slist fsort
            args' <- sequence (zipWith toAtom sorts args)
            return$ foldl Apply h args'
        _ -> throwError ("unexpected function argument {}; expected type {}"%[show t, show ty])
toAtom a t  = throwError ("some problem sort:{} term:{}"%[show a,show t])


--Given a something like "f x + g y", eliminate atoms to get a first order term
toTm :: Term -> Tfresh Term
toTm t@(Variable v) = do
    getSort t
    return t --assume it has integer sort
toTm t = do
    let (args,h) = tlist t
    case h of
        Constant c -> do
            check (isIlaFn c) ("bad Constant {}(integer expected)"%[c])
            ts <- mapM (toTm) args
            return$ foldl Apply h ts
        Variable vhead -> do
            isint <- isInt vhead
            if isint then
                check (args==[]) ("trying to apply an integer: {}"%[show t]) >> return t
              else do
                v' <- freshVar
                --vatom <- toAtom
                veq <- transformInt t v'
                tell (aexists v' Int . aand veq)
                return (Variable v')
        _ -> throwError$ "bad Form (term expected)\nreceived: "++show t


rhoify :: Sort -> Either String Sort
rhoify Int = return$ Arrow Int Bool
rhoify (Arrow Int b) = liftM (Arrow Int) $ rhoify b
rhoify (Arrow a b) = liftM2 Arrow (rhoify a) (rhoify b)
rhoify Bool = throwError "bad sort"

--the method we really need, should be used in place of getsort
isInt :: Variable -> Tfresh Bool
isInt v = do
    ms <- reader (lookup v)
    maybe (throwError ("Can't find sort of variable "++v)) (return.(==Int)) ms


--given a term with sort Int, and  a return variable r,
-- produces a term with sort Bool such that if x is assigned to r,
-- the new term should evaluate to true iff the old one would evaluate to x
transformInt :: Term -> Variable -> Tfresh Term
transformInt t@(Variable x) v = return$ aequals t (Variable v)
transformInt t@(Constant c) v =
    if all (`elem` ['0'..'9']) c then return$ aequals t (Variable v)
        else throwError ("non-numerical constant: "++c)
--need to be careful with the state - the branch not taken may introduce
-- unneccessary conditions
transformInt (If cond thn els) v = do
    condt <- transformBool cond
    condn <- neg condt
    thnt <- extractTerm$ transformInt thn v
    elst <- extractTerm$ transformInt els v
    --condn <- transformBool n
    return (aor (aand condt thnt) (aand condn elst))
transformInt t@(Apply _ _) v = do
    let (args,h) = tlist t
    case h of
        (Constant _) -> do
            tm <- toTm t
            return$ aequals tm (Variable v)
        (Variable f) -> do
            fsort <- varSort f
            let (sorts,Bool) = slist fsort
            args' <- sequence (zipWith toAtom sorts args)
            return$ Apply (foldl Apply h args' ) (Variable v)

-- given a term with boolean sort, transform it into a goal clause in hohc format
transformBool :: Term -> Tfresh Term
transformBool (If cond thn els) = do
    condt <- transformBool cond
    condn <- neg condt
    thnt <- extractTerm$ transformBool thn
    elst <- extractTerm$ transformBool els
    return (aor (aand condt thnt) (aand condn elst))
transformBool t = let (args,h) = tlist t
                      withArgs fn = foldl Apply h <$> mapM (fn) args in
    case h of
        Constant c ->
            if (c `elem` logicalSymbols) then withArgs transformBool
            else if (c `elem` ilaRels) then withArgs toTm
            else if c == "assert" then check (length args == 1) "bad assert" >> transformBool (head args)
            else throwError$ "expecting boolean expression, got "++show t
        _ -> throwError$ "expecting boolean expression, got "++show t

--assumes all relevant symbols are binary operators
--the negation operator should be dealt with sooner
neg :: MonadError String m => Term -> m Term
neg (Apply (Constant "assert") y) = neg y
neg (If c th el) = do
    th' <- neg th
    el' <- neg el
    return $ If c th' el'
neg (Apply (Apply(Constant c) x) y)
    | c `elem` ilaRels = return$ Apply (Apply(Constant (invert c)) x) y
    | c `elem` logicalBinary = do
        x' <- neg x
        y' <- neg y
        return$ Apply (Apply(Constant (invert c)) x') y'
    | otherwise = throwError "bad condition (probably badly typed and I should have caught this earlier, report this)"
neg (Constant c)
    | c `elem` logicalConstants = return$ Constant (invert c)
    | otherwise = throwError "bad condition (probably badly typed and I should have caught this earlier, report this)"
neg other = throwError ("bad condition (not ila) containing "++ show other)

invert ">" = "<="
invert ">=" = "<"
invert "<" = ">="
invert "<=" = ">"
invert "=" = "≠"
invert "≠" = "="
invert "∨" = "∧"
invert "∧" = "∨"
invert "true" = "false"
invert "false" = "true"

-- given `X t1 t2`, returns ([t1,t2],"X")
tlist :: Term -> ([Term],Term)
tlist = tlist' []

tlist' :: [Term] -> Term -> ([Term],Term)
tlist' ts (Apply a t) = tlist' (t:ts) a
tlist' ts t = (ts,t)

-- given `s1->s2->Bool` returns ([s1,s2],Bool)
slist :: Sort -> ([Sort],Sort)
slist Bool = ([],Bool)
slist Int = ([],Int)
slist (Arrow a b) = let (as,x) = slist b in (a:as,x)

occursIn :: Variable -> Term -> Bool
occursIn x (Variable v) = x==v
occursIn x (Constant _) = False
occursIn x (Apply a b) = x `occursIn` a || x `occursIn` b
occursIn x (Lambda y _ t) = x/=y && x `occursIn` t
