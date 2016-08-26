module Transform--(transform,checkHorn)
    where

import DataTypes
import Data.Maybe(fromJust)
import Inference(replaceInTerm)
import Parser(qp)


transform :: DeltaEnv -> Term -> (String,Term)
transform e (Apply (Apply (Constant "⇒") a) b) =
    if length vs /= length ss 
       then error "we have a problem"
       else (vb,foldr (\ (v,s) term -> (Lambda v s term)) a (zip vs ss))
    where (vs,vb) = vlist b
          (ss,sb) = slist $ fromJust $ lookup vb e
    

split (Apply (Apply (Constant "⇒") a) b) = (a,vlist b)

vlist :: Term -> ([String],String)
vlist = vlist' []

vlist' :: [String] -> Term -> ([String],String)
vlist' vs (Variable b) = (vs,b)
vlist' vs (Apply a (Variable v)) = vlist' (v:vs) a
vlist' vs x = error (show x)

slist :: Sort -> ([Sort],Sort)
slist Bool = ([],Bool)
slist (Arrow a b) = (a:as,x)
    where (as,x) = slist b

    
checkHorn :: DeltaEnv -> [Term] -> [(String,Term)]
checkHorn e = map (transform e)


--this does not do any checking, that should be done beforehand
transformProg :: DeltaEnv -> [Term] -> [(Variable,Term)] --this is called (| |) in the paper
transformProg d ts = map f d
    where
        txsys = map split ts
        f (v,s) = (v,foldr (\ (v,s) term -> (Lambda v s term)) conj (zip vs (fst$slist s)))
            where
                txss = [(t,xs) | (t,(xs,y))<-txsys, y==v]
                vs = snd $ head txss
                conj = foldl1 aand (map fst txss)
                --could create fresh variables here, but that would make it harder to read the output
                --for now, just assume the input is nice
