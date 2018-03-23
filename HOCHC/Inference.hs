{-
This is an implementation of the 'algorithm from inference rules' described in chapter 5.
-}

module HOCHC.Inference
    where

import HOCHC.DataTypes
import HOCHC.Parser
import HOCHC.Fresh

import Data.List(lookup)
import Data.Maybe(fromJust,fromMaybe)
import Data.Char(isDigit)

import Control.Applicative
import Control.Monad.Except(throwError)

import HOCHC.Utils

(↦) = (,)

isFm ::[Variable] -> Term -> Bool -- does not check the sort
isFm vars (Constant c) = isIlaSymbol c
isFm vars (Variable x) = x `elem` vars
isFm vars (Apply t1 t2) = isFm vars t1 && isFm vars t2
isFm vars _ = False

-- Flattens a type enviroment into a sort environment
flatenv :: Gamma -> DeltaEnv
flatenv = map (\(x,ty)->(x, flat ty))

infer :: Gamma -> Term -> Mfresh (DeltaEnv,Term,MonoType)
infer g (Variable v) = do
    ty <- case lookup v g of
               Just x -> return x
               Nothing -> throwError (v++" not found")
    return ([], Constant "true", ty) --(Var)
    where
        ty = case lookup v g of
                          Just x -> x
                          Nothing -> error (v++" not found")
infer g (Apply (Apply (Constant "∧") t1) t2) = do
    (d1,c1,BoolT phi) <- infer g t1
    (d2,c2,BoolT psi) <- infer g t2
    return (d1++d2,aand c1 c2,BoolT (aand phi psi))--(And)
infer g (Apply (Apply (Constant "∨") t1) t2) = do
    (d1,c1,BoolT phi) <- infer g t1
    (d2,c2,BoolT psi) <- infer g t2
    return (d1++d2,aand c1 c2,BoolT (aor phi psi))--(Or)
infer g (Apply (Constant "∃") (Lambda x Int t)) = do
    v <- freshVar
    (d,c,BoolT phi) <-infer ((v,IntT):g) (replaceInTerm [(x,Variable v)] t)--(Exists)
    return (d,aforall v Int c,BoolT (aexists v Int phi))
infer g t
    | isFm [x | (x,t)<-g , t==IntT] t = return ([], Constant "true", BoolT t)--(Constraint)
infer g (Apply t1 t2) = do
    (d1,c1,ty) <- infer g t1
    case ty of
         (ArrowT x IntT ty)-> return
             (d1,c1,replaceInMT [x ↦ t2] ty)--(AppI)
         (ArrowT _ ty1 ty) -> do
             (d2,c2,ty2) <- infer g t2
             c3 <- inferSub ty2 ty1
             return (d1++d2, aand (aand c1 c2) c3, ty)--(AppR)
         _ -> throwError ("applying term with non-function type\n"++
                          show (d1,c1,ty) ++show t1 ++ show t2++";"++show g)

infer g (Lambda x Int t) = do
    v <- freshVar
    (d1,c,ty) <- infer ((v,IntT):g) (replaceInTerm [x ↦ Variable v] t)
    return (d1,aforall v Int c,ArrowT v IntT ty)--(AbsI)
infer g (Lambda x s t) = do
    v <- freshVar
    (ty1,d1) <- freshTy (flatenv g) s
    (d2,c,ty2) <- infer ((v,ty1):g) (replaceInTerm [x ↦ Variable v] t)
    return (d1++d2,c,ArrowT "_" ty1 ty2) --(AbsR)
infer g t = throwError ("bad part of clause " ++ show t)

inferSub :: MonoType -> MonoType -> Mfresh Term
inferSub (BoolT t1) (BoolT t2) = return $ aimplies t1 t2 --(SubBool)
inferSub (ArrowT x IntT ty) (ArrowT y IntT ty_) = do
    z <- freshVar
    c <- inferSub (replaceInMT [x ↦ Variable z] ty) (replaceInMT [y ↦ Variable z] ty_)
    return $ aforall z Int c--(SubI)
inferSub (ArrowT "_" ty1 ty2) (ArrowT "_" ty1_ ty2_) = do
    c1 <- inferSub ty1_ ty1
    c2 <- inferSub ty2 ty2_
    return $ aand c1 c2--(SubR)
inferSub x y = throwError (unlines ["type error",show x,show y])


inferProg :: DeltaEnv -> [(Variable,Term)] -> Mfresh (DeltaEnv, Gamma, Term)
inferProg d prog= errorPart "Inference" (do
    (g,d') <- freshEnv d
    (ds,cs,tys) <- unzip3 <$> mapM (infer g) ts
    c2s <- sequence (zipWith inferSub tys (map (fromJust.flip lookup g) vs))
    return (d'++concat ds,g,foldl1 aand (zipWith aand cs c2s)))
    where (vs,ts) = unzip prog
