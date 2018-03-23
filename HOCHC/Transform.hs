{-
Functions for transforming a higher-order constrained Horn clause problem into a logic safety problem
See Section 3.2.
-}

module HOCHC.Transform(transformProg,vlist,slist,split,occursIn, elim,split')
    where

import HOCHC.Fresh(Mfresh,freshVar)
import HOCHC.DataTypes
import HOCHC.Utils
import HOCHC.FormulaChecks(checkSort)

import Data.Maybe(fromJust)
import Control.Monad(liftM,liftM2)
import Control.Monad.Except(throwError,lift)


infixl 1 `unless`

unless :: String -> Bool -> Mfresh ()
unless err cond = if cond then return () else throwError err



-- turns `P y z => X y z` into (`P x y`,(["y","z"],"X"))
-- possibly returns an error
split ::Term -> Either String (Term,([String],String))
split t = do
    let (vss,t1) = getQuants t
    (t2,(vs,v)) <- split' t1
    let vss2 = filter (not.(`elem` vs).fst) vss
    return (foldr (\ (x,s) tb -> (Apply (Constant "∃") (Lambda x s tb))) t2 vss2,(vs,v))

split' ::Term -> Either String (Term,([String],String))
split' (Apply (Apply (Constant "⇒") a) b) = vlist b >>= return . (,) a
split' t = Left ("not in Horn clause format\n"++show t)

-- given `X y z`, returns (["y","z"],"X")
vlist :: Term -> Either String ([String],String)
vlist = vlist' []

vlist' :: [String] -> Term -> Either String ([String],String)
vlist' vs (Variable b) = Right (vs,b)
vlist' vs (Apply a (Variable v)) = vlist' (v:vs) a
vlist' vs x = Left ("bad RHS: "++show x)

-- given `s1->s2->Bool` returns ([s1,s2],Bool)
slist :: Sort -> Either String ([Sort],Sort)
slist Bool = Right ([],Bool)
slist (Arrow a b) = do
    (as,x) <- slist b
    Right (a:as,x)
slist Int = Left "Non-relational sort"

occursIn :: Variable -> Term -> Bool
occursIn x (Variable v) = x==v
occursIn x (Constant _) = False
occursIn x (Apply a b) = x `occursIn` a || x `occursIn` b
occursIn x (Lambda y _ t) = x/=y && x `occursIn` t

-- Transforms a program as given in Section 3.2
-- turns foralls into lambdas and combines clauses with the same head
transformProg :: DeltaEnv -> [Term] -> Mfresh [(Variable,Term)]
transformProg d ts = errorPart "Transformation" $ do
    txsys <- lift $ mapM split ts
    let f (v,s) = do
            (ss,sb)<- lift $ slist s
            let txsys' = [(t,(xs,y)) | (t,(xs,y))<-txsys, y==v]
            unlines ["unexpected number of arguments to {}" % [v],
                     "expected {}" % [show (length ss)]
                    ] `unless` (all ((length ss==).length.fst.snd) txsys')
            vs <- mapM (const freshVar) ss
            let ts = [replaceInTerm (zip xs (map Variable vs)) t | (t,(xs,y))<-txsys']
            "No clauses given for {}"%[v] `unless` ts/=[]
            lift $ mapM (checkSort (zip vs ss ++ d)) ts
            return (v,foldr (\ (v,s) term -> Lambda v s term) (foldl1 aor ts) (zip vs ss))
    mapM f d


-- Eliminate type guards. See Section 4.3.
elim :: Term -> Mfresh Term
elim (ExistsT x ty t) = do ll <- lar (Constant "false") ty
                           elim (replaceInTerm [(x,ll)] t)
elim (Lambda x s t)   = liftM (Lambda x s) (elim t)
elim (Apply a b)      = liftM2 Apply (elim a) (elim b)
elim (Constant c)     = return $ Constant c
elim (Variable x)     = return $ Variable x

com :: MonoType -> Term -> Mfresh Term
com (BoolT phi) z = return $ aand z (Apply (Constant "¬") phi)
com (ArrowT x IntT ty) z = com ty (Apply z $ Variable x) >>= return . aexists x Int
com (ArrowT "_" ty1 ty2) z = lar (Constant "false") ty1 >>= com ty2 . Apply z

lar :: Term -> MonoType -> Mfresh Term
lar g (BoolT phi) = return $ aor g phi
lar g (ArrowT x IntT ty) = liftM (Lambda x Int) (lar g ty)
lar g (ArrowT "_" ty1 ty2) = do
  z <- freshVar
  c <- com ty1 (Variable z)
  liftM (Lambda z Int) (lar (aor g c) ty2)
