module Transform(transform,checkHorn,transformProg,vlist,slist,split,occursIn, elim)
    where

import Fresh(Mfresh,freshVar)
import DataTypes
import Tools
import FormulaChecks(checkSort)
import Data.Maybe(fromJust)
import Control.Monad(liftM,liftM2)

--Based on section 4 of the paper.

transform d t = errorPart "Transformation" $ transform' d t

transform' :: DeltaEnv -> Term -> Either String (String,Term)
transform' e (Apply (Apply (Constant "⇒") a) b) = do
    (vs,vb) <- vlist b
    (ss,sb) <- slist $ fromJust $ lookup vb e
    if length vs /= length ss 
        then Left $ unlines [
            "unexpected number of arguments",
            "given "++show (length vs)++": "++show b,
            "expected "++show (length ss)]
        else Right (vb,foldr (\ (v,s) term -> (Lambda v s term)) a (zip vs ss))
transform' _ _ = Left "Bad format"

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
split' _ = Left "not in Horn clause format"

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

-- transforms a list of clauses, only used in tests
checkHorn :: DeltaEnv -> [Term] -> Either String [(String,Term)]
checkHorn e = mapM (transform e)

occursIn :: Variable -> Term -> Bool
occursIn x (Variable v) = x==v
occursIn x (Constant _) = False
occursIn x (Apply a b) = x `occursIn` a || x `occursIn` b
occursIn x (Lambda y _ t) = x/=y && x `occursIn` t

-- Transforms a program as given in Section 4(Reduction to program evaluation) of the paper
-- turns foralls into lambdas and combines clauses with the same head
transformProg :: DeltaEnv -> [Term] -> Either String [(Variable,Term)] --this is called (| |) in the paper
transformProg d ts = errorPart "Transformation" $ do
    txsys <- mapM split ts
    let f (v,s) = do
            (ss,sb)<- slist s
            "No clauses given for {}"%[v] `unless` ts/=[]
            "non-matching arguments for {}"%[v] `unless` all (==vs) xss
            unlines ["unexpected number of arguments to {}" % [v],
                     "given {}" % [show (length vs)],
                     "expected {}" % [show (length ss)]
                    ] `unless` length vs == length ss
            mapM (checkSort (zip vs ss ++ d)) ts
            Right (v,foldr (\ (v,s) term -> Lambda v s term) disj (zip vs ss))
            where
                (ts,xss) = unzip [(t,xs) | (t,(xs,y))<-txsys, y==v]
                vs = head xss
                disj = foldl1 aor ts
    mapM f d

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