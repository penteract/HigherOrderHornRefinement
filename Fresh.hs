module Fresh(freshVar,freshRel,freshTy,freshEnv,
    fromM,Mfresh)
    where

import DataTypes

import Control.Monad (liftM, ap)
import Control.Applicative
--import Data.Functor

newtype Mfresh a = Mfresh {fromM :: (Int -> (a,Int))}

instance Monad Mfresh where
    return x = Mfresh (\n->(x,n))
    (>>=) (Mfresh xm) f = Mfresh (\n->let (x,m) = xm n in fromM (f x) m)

instance Functor Mfresh where
    fmap = liftM
instance Applicative Mfresh where 
    pure = return
    (<*>) = ap
    
freshVar :: Mfresh Variable
freshVar = Mfresh freshVar'
freshVar' n = ("x_"++show n,n+1)
    
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
    return (zip (map fst delta) (map ((,)[]) tys), concat ds)