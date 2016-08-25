module Inference
    where

import DataTypes
import Parser
import Data.List(lookup)
import Data.Maybe(fromJust,fromMaybe)
import Data.Char(isDigit)

import Control.Monad (liftM, ap)

(%) :: String -> [String] -> String
(%) s [] = s
(%) ('{':'}':s) (x:xs) = x++(s%xs)
(%) ('\\':c:s) xs = c:(s%xs)
(%) (c:s) xs = c:(s%xs)
(%) "" _ = error "not enough '{}' in string"


flatenv :: Gamma -> DeltaEnv
flatenv = map (\(a,b)->(a,flat $ snd b))

ilaGamma :: Gamma
ilaGamma = 
    (zip ilaOps $ repeat ([],(ArrowT "_" IntT (ArrowT "_" IntT IntT))))
  ++ map (\ r -> (r,([],ArrowT "x" IntT . ArrowT "y" IntT $ BoolT (qp ("x {} y"%[r]))))) ilaRels
  ++ map (\ r -> (r,
            ([("X",Bool),("Y",Bool)],ArrowT "_" (BoolT (qp "X")) . ArrowT "_" (BoolT (qp "Y")) $ BoolT (qp ("X {} Y"%[r])))))
         logicalBinary
  ++ map (\ r -> (r,
            ([("X",Bool)],ArrowT "_" (BoolT (qp "X")) $ BoolT (qp (r++" Y")))))
         logicalUnary
  ++ [("∃", ([("X",Arrow Int Bool)], --This one might be more complicated
    ArrowT "_" (ArrowT "x" IntT (BoolT $ qp "X x") ) (BoolT $ qp "∃x:int.X x")))]


getTyOfConst :: Constant -> Scheme
getTyOfConst c
    | c `elem` ilaOps = ([],(ArrowT "_" IntT (ArrowT "_" IntT IntT)))
    | c `elem` ilaRels = ([],ArrowT "x" IntT . ArrowT "y" IntT $ BoolT (qp ("x {} y"%[c])))
    | c `elem` logicalBinary =
        ([("X",Bool),("Y",Bool)],
         ArrowT "_" (BoolT (qp "X")).ArrowT "_" (BoolT (qp "Y")) $ BoolT (qp ("X {} Y"%[c])))
    | c `elem` logicalUnary =
        ([("X",Bool)],
         ArrowT "_" (BoolT (qp "X")) $ BoolT (qp ("{} X"%[c])))
    | c `elem` logicalQuantifiers = -- what if it's not quantifying over ints?
        ([("X",Bool)],
            ArrowT "_" (ArrowT "x" IntT (BoolT $ qp "X x") ) (BoolT $ qp ("{} x:int.X x"%[c])))
    | all isDigit c = ([],IntT)
    
replaceInMT :: [(Variable,Term)] -> MonoType -> MonoType
replaceInMT rs IntT = IntT
replaceInMT rs (BoolT t) = BoolT (replaceInTerm rs t)
replaceInMT rs (ArrowT x t1 t2) = --may cause problems if a variable in rs becomes bound
    ArrowT x (replaceInMT rs t1) (replaceInMT rs_ t2)
    where rs_ = filter (\(a,b) -> a/=x) rs

replaceInTerm :: [(Variable,Term)] -> Term -> Term
replaceInTerm rs (Apply t1 t2) = Apply (replaceInTerm rs t1) (replaceInTerm rs t2)
replaceInTerm rs (Lambda x s t) = --may cause problems if a variable in rs becomes bound
    Lambda x s (replaceInTerm (filter (\(a,b) -> a/=x) rs) t)
replaceInTerm rs (Variable v) = fromMaybe (Variable v) (lookup v rs)
replaceInTerm rs (Constant c) = (Constant c)


newtype Mfresh a = Mfresh {fromM :: (Int -> (a,Int))}

{-f a b c = a.c.b
        = (.) a ((.)c b)
        = (.) a (flip (.) b c)
        = (.) a . flip (.) b
        
        
        = (.) ((.) a c) b
        = flip (.) b ((.) a c)
        = flip (.) b . (.) a-}

instance Monad Mfresh where
    return x = Mfresh (\n->(x,n))
    --(>>=) (Mfresh xm) f = Mfresh (\n->let (x,m) = xm n in fromM (f x) m)
    --(>>=) xm f = Mfresh $ uncurry (fromM.f) . fromM xm
    (>>=) = (. (uncurry . (.)fromM)) . (.) Mfresh .(flip (.) . fromM)
    --(>>=) = flip (.) uncurry . flip (.) 


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
    (ts,ds) <- sequence (map (freshRel (flatenv g)) ss) >>= return.unzip
    return (ds,Constant "true",replaceInMT (zip vs ts) ty)--(IConst)
    where 
        (targs,ty) = getTyOfConst c
        (vs,ss) = unzip targs
infer g (Apply t1 t2) = do
    aaa <- infer g t1
    (d1,c1,x,ty1,ty) <- return (case aaa of
              (d1,c1,(ArrowT x ty1 ty))->(d1,c1,x,ty1,ty)
              _ -> error (show aaa ++show t1 ++ show t2++";"++show g)
              )
    (d2,c2,ty2) <- infer g t2
    c3 <- inferSub ty2 ty1
    return (d1, aand (aand c1 c2) c3, replaceInMT [(x,t2)] ty) --(IApp)
infer g (Lambda x Int t) = do
    (d1,c,ty) <- infer ((x,([],IntT)):g) t
    return (d1,aforall x Int c,ArrowT x IntT ty)--(IProd)
infer g (Lambda x s t) = do
        (ty1,d1) <- freshTy (flatenv g) s
        (d2,c,ty2) <- infer ((x,([],ty1)):g) t
        return (d2++d1,c,ArrowT "_" ty1 ty2) --(IArrow)

inferSub :: MonoType -> MonoType -> Mfresh Term
inferSub IntT IntT = return $ Constant "true"
inferSub (BoolT t1) (BoolT t2) = return$replaceInTerm [("s",t1),("t",t2)] (qp "s=>t")
inferSub (ArrowT x IntT ty) (ArrowT y IntT ty_) = do
    z <- freshVar
    c <- inferSub (replaceInMT [(x,Variable z)] ty) (replaceInMT [(y,Variable z)] ty_)
    return$aforall z Int c
inferSub (ArrowT "_" ty1 ty2) (ArrowT "_" ty1_ ty2_) = do
    c1 <- inferSub ty1_ ty1
    c2 <- inferSub ty2 ty2_
    return $ aand c1 c2
inferSub _ _ = error "type error"
