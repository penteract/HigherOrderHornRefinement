module Transform(transform,checkHorn,transformProg,vlist,split)
    where

import DataTypes
import Tools
import Data.Maybe(fromJust)
--import Inference(replaceInTerm)

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
    
split ::Term -> Either String (Term,([String],String))
split t = do
    let (vss,t1) = getQuants t
    (t2,(vs,v)) <- split' t1
    let vss2 = filter (not.(`elem` vs).fst) vss
    return (foldr (\ (x,s) tb -> (Apply (Constant "∃") (Lambda x s tb))) t2 vss2,(vs,v))

split' ::Term -> Either String (Term,([String],String))
split' (Apply (Apply (Constant "⇒") a) b) = vlist b >>= return . (,) a
split' _ = Left "not in Horn clause format"

vlist :: Term -> Either String ([String],String)
vlist = vlist' []

vlist' :: [String] -> Term -> Either String ([String],String)
vlist' vs (Variable b) = Right (vs,b)
vlist' vs (Apply a (Variable v)) = vlist' (v:vs) a
vlist' vs x = Left ("bad RHS: "++show x)

slist :: Sort -> Either String ([Sort],Sort)
slist Bool = Right ([],Bool)
slist (Arrow a b) = do
    (as,x) <- slist b
    Right (a:as,x)
slist Int = Left "Non-relational sort"

    
checkHorn :: DeltaEnv -> [Term] -> Either String [(String,Term)]
checkHorn e = mapM (transform e)

occursIn :: Variable -> Term -> Bool
occursIn x (Variable v) = x==v
occursIn x (Constant _) = False
occursIn x (Apply a b) = x `occursIn` a || x `occursIn` b
occursIn x (Lambda y _ t) = x/=y && x `occursIn` t

--does not yet do sort checking
transformProg :: DeltaEnv -> [Term] -> Either String [(Variable,Term)] --this is called (| |) in the paper
transformProg d ts = errorPart "Transformation" $ do
    txsys <- mapM split ts
    let f (v,s) = do
            (ss,sb)<- slist s
            if txss==[] then Left ("No clauses given for {}"%[v]) else Right ()
            if not (all ((==vs).snd) txss) then
                Left ("non-matching arguments for {}"%[v]) else Right ()--could create fresh variables here, but that would make it harder to read the output
            if length vs /= length ss
                then Left $ unlines [
                    "unexpected number of arguments",
                    "given {}: {}" % [show (length vs), show b],
                    "expected {}" % [show (length ss)]]
                else Right ()
            Right (v,foldr (\ (v,s) term -> Lambda v s term) conj (zip vs ss))
            where
                txss = [(t,xs) | (t,(xs,y))<-txsys, y==v]
                (b,vs) = head txss
                conj = foldl1 aand (map fst txss)
    mapM f d
