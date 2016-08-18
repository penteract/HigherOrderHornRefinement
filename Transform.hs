module Transform(transform,checkHorn)
    where

import DataTypes
import Data.Maybe(fromJust)


transform :: DeltaEnv -> Term -> (String,Term)
transform e (Apply (Apply (Constant "⇒") a) b) =
    if length vs /= length ss 
       then error "we have a problem"
       else (vb,foldr (\ (v,s) term -> (Lambda v s term)) a (zip vs ss))
    where (vs,vb) = vlist b
          s = fromJust $ lookup vb e
          (ss,sb) = slist s
    


vlist :: Term -> ([String],String)
vlist = vlist' []

vlist' :: [String] -> Term -> ([String],String)
vlist' vs (Variable b) = (vs,b)
vlist' vs (Apply a (Variable v)) = vlist' (v:vs) a

slist :: Sort -> ([Sort],Sort)
slist Bool = ([],Bool)
slist (Arrow a b) = (a:as,x)
    where (as,x) = slist b

    
checkHorn :: DeltaEnv -> [Term] -> [(String,Term)]
checkHorn e = map (transform e)
