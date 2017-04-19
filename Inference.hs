module Inference
    where

import DataTypes
import Parser
import Fresh

import Data.List(lookup)
import Data.Maybe(fromJust,fromMaybe)
import Data.Char(isDigit)

import Control.Monad --(liftM, ap)
import Control.Applicative

import Tools

-- See section 6 (Type inference) of the Paper. This is an implementation of the inference relations defined there.


--flattens a type enviroment into a sort environment
flatenv :: Gamma -> DeltaEnv
flatenv = map (\(x,(_,ty))->(x, flat ty))

getTyOfConst :: Constant -> Mfresh Scheme
getTyOfConst c
    | c `elem` ilaOps = return ([],(ArrowT "_" IntT (ArrowT "_" IntT IntT)))
    | c `elem` ilaRels = return ([],ArrowT "x_" IntT . ArrowT "y_" IntT $ BoolT (qp ("x_ {} y_"%[c])))
    | c `elem` logicalBinary =
        return ([("X",Bool),("Y",Bool)],
         ArrowT "_" (BoolT (qp "X")).ArrowT "_" (BoolT (qp "Y")) $ BoolT (qp ("X {} Y"%[c])))
    | c `elem` logicalUnary =
        return ([("X",Bool)],
         ArrowT "_" (BoolT (qp "X")) $ BoolT (qp ("{} X"%[c])))
    | c `elem` logicalQuantifiers = -- what if it's not quantifying over ints?
        do
        x <- freshVar
        return ([("X",Arrow Int Bool)],
            ArrowT "_" (ArrowT "x_" IntT (BoolT $ qp "X x_") ) (BoolT $ qp ("{} {}:int.X {}"%[c,x,x])))
    | c `elem` logicalConstants = return ([],BoolT (Constant c))
    | all isDigit c = return ([],IntT)
    | otherwise = lift (Left ("unknown constant"++c))


infer :: Gamma -> Term -> Mfresh (DeltaEnv,Term,MonoType)
infer g (Variable v) = do
    (ts,ds) <- sequence (map (freshRel (flatenv g)) ss) >>= return.unzip
    return (ds,Constant "true",replaceInMT (zip vs ts) ty)--(IVar)
    where 
        (targs,ty) = case lookup v g of
                          Just x -> x
                          Nothing -> error (v++" not found")
        (vs,ss) = unzip targs
infer g (Constant c) = do
    (targs,ty) <- getTyOfConst c
    let (vs,ss) = unzip targs
    (ts,ds) <- unzip <$> mapM (freshRel (flatenv g)) ss
    return (ds,Constant "true",replaceInMT (zip vs ts) ty)--(IConst)
infer g (Apply t1 t2) = do
    aaa <- infer g t1
    (d1,c1,x,ty1,ty) <- return (case aaa of
              (d1,c1,(ArrowT x ty1 ty))->(d1,c1,x,ty1,ty)
              _ -> error (show aaa ++show t1 ++ show t2++";"++show g)
              )
    (d2,c2,ty2) <- infer g t2
    c3 <- inferSub ty2 ty1
    return (d1++d2, aand (aand c1 c2) c3, replaceInMT [(x,t2)] ty) --(IApp)  (paper currently uses d1 rather than d1++d2, but this works better)
infer g (Lambda x Int t) = do
    v <- freshVar
    (d1,c,ty) <- infer ((v,([],IntT)):g) (replaceInTerm [(x,Variable v)] t)
    return (d1,aforall v Int c,ArrowT v IntT ty)--(IProd)
infer g (Lambda x s t) = do
    v <- freshVar
    (ty1,d1) <- freshTy (flatenv g) s
    (d2,c,ty2) <- infer ((v,([],ty1)):g) (replaceInTerm [(x,Variable v)] t)
    return (d1++d2,c,ArrowT "_" ty1 ty2) --(IArrow)

inferSub :: MonoType -> MonoType -> Mfresh Term
inferSub IntT IntT = return $ Constant "true"
inferSub (BoolT t1) (BoolT t2) = return $ aimplies t1 t2
inferSub (ArrowT x IntT ty) (ArrowT y IntT ty_) = do
    z <- freshVar
    c <- inferSub (replaceInMT [(x,Variable z)] ty) (replaceInMT [(y,Variable z)] ty_)
    return$aforall z Int c
inferSub (ArrowT "_" ty1 ty2) (ArrowT "_" ty1_ ty2_) = do
    c1 <- inferSub ty1_ ty1
    c2 <- inferSub ty2 ty2_
    return $ aand c1 c2
inferSub x y = lift $ Left (unlines ["type error",show x,show y])


inferProg :: DeltaEnv -> [(Variable,Term)] -> Mfresh (DeltaEnv, Gamma, Term)
inferProg d prog= do
    (g,d') <- freshEnv d
    (ds,cs,tys) <- unzip3 <$> mapM (infer g) ts
    c2s <- sequence (zipWith inferSub tys (map(snd.fromJust.flip lookup g) vs))
    return (d'++concat ds,g,foldl1 aand (zipWith aand cs c2s))
    where (vs,ts) = unzip prog
