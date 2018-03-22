{-
Implements the judgement freshTy given in Chapter 5.

Also defines the monad Mfresh in which these judgements can be expressed
-}

module HOCHC.Fresh(freshVar, freshVarx,freshRel,freshTy,freshEnv,
    Mfresh, lift, runStateT, runFresh)
    where


import HOCHC.DataTypes
import Control.Monad (liftM, ap)
import Control.Applicative

import Control.Monad.State
import Control.Monad.Except


type Mfresh = StateT Int (Either String)

freshVar :: Mfresh Variable
freshVar = state (\n->("x_"++show n,n+1))

freshVarx :: Variable -> Mfresh Variable
freshVarx x = state (\n->(x++"_"++show n,n+1))

runFresh :: Monad m => StateT Int m a -> m a
runFresh = flip evalStateT 0

freshRel :: DeltaEnv -> Sort -> Mfresh (Term,(Variable,Sort))
freshRel d rho = do
    x<-freshVar
    return (foldl (\ t y -> Apply t (Variable y)) (Variable x) ys,
                    (x,iterate (Arrow Int) rho !! length ys))
    where ys = map fst $ filter ((==Int).snd) d


freshTy :: DeltaEnv -> Sort -> Mfresh (MonoType,DeltaEnv)
freshTy d Bool = do (t,d) <- freshRel d Bool
                    return (BoolT t,[d])
freshTy d Int = return (IntT,[])
freshTy d (Arrow Int s) = do
    z <- freshVar
    (ty,ds)<-freshTy ((z,Int):d) s
    return $ (ArrowT z IntT ty ,ds)
freshTy d (Arrow s1 s2) = do
    (ty1,d1) <- freshTy d s1
    (ty2,d2) <- freshTy d s2
    return (ArrowT "_" ty1 ty2,d2++d1)


freshEnv :: DeltaEnv -> Mfresh (Gamma,DeltaEnv)
freshEnv delta = do
    (tys,ds) <- unzip <$> (sequence $ map (freshTy [] . snd) delta)
    return (zip (map fst delta) tys, concat ds)
