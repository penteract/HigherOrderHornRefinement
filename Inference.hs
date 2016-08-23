module Inference
    where

import DataTypes
import Parser
import Data.List(lookup)
import Data.Maybe(fromJust)
import Data.Char(isDigit)

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


getTyOfConst :: Const -> Scheme
getTyOfConst c
    | c `elem` ilaOps = ([],(ArrowT "_" IntT (ArrowT "_" IntT IntT)))
    | c `elem` ilaRels = ([],ArrowT "x" IntT . ArrowT "y" IntT $ BoolT (qp ("x {} y"%[c])))
    | c `elem` logicalBinary =
        ([("X",Bool),("Y",Bool)],
         ArrowT "_" (BoolT (qp "X")).ArrowT "_" (BoolT (qp "Y")) $ BoolT (qp ("X {} Y"%[c])))
    | c `elem` logicalUnary =
        ([("X",Bool)],
         ArrowT "_" (BoolT (qp "Y")) $ BoolT (qp ("{} X"%[c])))
    | all isDigit c = ([],IntT)
    
replaceInMT :: [(Variable,Term)] -> MonoType -> MonoType
replaceInMT rs IntT = IntT
replaceInMT rs (BoolT t) = BoolT (replaceInTerm rs t)
replaceInMT rs (ArrowT x t1 t2) = ArrowT x (replaceInMT rs t1) (replaceInMT rs_ t2)
    where rs_ = filter (\(a,b) -> a!=x) rs

replaceInTerm :: [(Variable,Term)] -> Term -> Term
replaceInTerm rs (Apply t1 t2) = Arrow (replaceInTerm rs t1) (replaceInTerm r2 t2)
replaceInTerm rs (Lambda x s t) = Lambda x s (replaceInTerm (filter (\(a,b) -> a!=x) rs) t)
replaceInTerm rs (Variable v) = fromMaybe (Variable v) (lookup v rs)
replaceInTerm rs (Constant c) = (Constant c)


type Mfresh a = DeltaEnv -> (a,Int)

instance Monad Mfresh where
    return x n = (x,n)
    --(>>=) xm f n = let (x,m) = xm n in f x m 
    --    uncurry f (xm n)--uncurry f.xm --flip (.) xm . uncurry-- flip (.) uncurry . flip (.)
    (>>=) = flip (.) uncurry . flip (.) -- I had to --(. uncurry) . flip (.)

freshVar :: Mfresh Variable
freshVar n = ("_x"++show n,n+1)
    
freshRel :: DeltaEnv -> Sort -> Mfresh (Term,(Variable,Sort))
freshRel d rho n = ((foldl (\ t y -> Apply t (Variable y)) (Variable x) ys,
                    (x,iterate (Arrow Int) rho !! length xs)),n+1)
    where ys = map fst $ filter ((==Int).snd) d
          x = "_x" ++ show n

freshTy :: DeltaEnv -> Sort -> Mfresh (MonoType,DeltaEnv)
freshTy d Bool = do (t,d) <- freshRel d Bool
                    return (BoolT t,[d])
freshTy d Int = return (IntT,[])
freshTy d (Arrow Int s) = do
    z <- freshVar
    freshTy ((z,Int):d) s
freshTy d (Arrow s1 s2) = do
    (ty1,d1) <- freshTy d s1
    (ty2,d2) <- freshTy d s2
    return (ArrowT "_" ty1 ty2,d2++d1)



infer :: Gamma -> Term -> (DeltaEnv,Term,MonoType)
infer g (Variable v) = (ds,qp "true",replaceInMT (zip vs ts) ty)--(IVar)
    where 
        (targs,ty) = fromJust$lookup v g
        (vs,ss) = unzip targs
        (ts,ds) = unzip.map freshRel $ ss
infer g (Constant c) = (ds,qp "true",replaceInMT (zip vs ts) ty)--(IConst)
    where 
        (targs,ty) = getTyOfConst c g
        (vs,ss) = unzip targs
        (ts,ds) = unzip.map freshRel $ ss
infer g (Apply t1 t2) = (d1,replaceInTerm [("X",c1),("Y",c2),("Z",c3)] (qp "X^Y^Z"),replaceInMT [(x,t2)] ty) --(IApp)
    where 
        (d1,c1,(ArrowT x ty1 ty)) = infer g t1
        (d2,c2,ty2) = infer ((x,t1):g) t1
        c3 = inferSub ty2 ty1
infer g (Lambda x Int t) = (d1,replaceInTerm [("X",c)] (qp ("A {}:int.X"%[x])),ArrowT x IntT ty)--(IProd)
    where 
        (d1,c,ty) = infer (("x",([],IntT)):g) t
infer g (Lambda x s t) = (d2++d1,c,ArrowT "_" ty1 ty2) --(IArrow)
    where 
        (d1,ty1) = freshTy (flatenv (\(a,b)->(a,flat $ snd b)) g)
        (d2,c,ty2) = infer ((x,([],ty1)):g) t

inferSub :: MonoType -> MonoType -> Term
inferSub IntT IntT = Constant "true"
inferSub (BoolT t1) (BoolT t2) = replaceInTerm [("s",t1),("t",t2)] (qp "s=>t")
inferSub (ArrowT x IntT ty) (ArrowT y IntT ty_) = replaceInTerm [("c",c)] (qp $ "A {}:int.c"%[z])
    where z = freshVar (ArrowT "_" ty ty_)
          c = inferSub (replaceInMT [(x,Variable z)] ty) (replaceInMT [(y,Variable z)] ty_)
inferSub (ArrowT "_" ty1 ty2) (ArrowT "_" ty1_ ty2_) = replaceInTerm [("X",c1),("Y",c2)] (qp "X^Y")
    where c1 = inferSub ty1_ ty1
          c2 = inferSub ty2 ty2_
inferSub _ _ = error "type error"          