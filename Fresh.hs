module Fresh(freshVar,freshRel,freshTy,freshEnv,
    Mfresh, lift,runStateT)
    where

--Implements the judgements freshVar, freshTy and freshRel given in section 6 (Type inference) the paper


import DataTypes
import Control.Monad (liftM, ap)
import Control.Applicative

import Control.Monad.State
import Control.Monad.Except

    
type Mfresh = StateT Int (Either String)

freshVar :: Mfresh Variable
freshVar = state (\n->("x_"++show n,n+1))

    
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
