{-
This should do type inference, type checking and check that variables are bound
-}
module TypeCheck(typeCheck)
    where

import HOCHC.DataTypes
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map.Strict as M
import System.IO.Unsafe


typeCheck :: [Definition] -> Either String DeltaEnv
typeCheck defns = do
    sorts <- evalStateT (checkInMonad defns) (PartialEnv M.empty M.empty)
    return$ zip (map (\(v,_,_) -> v) defns) sorts

checkInMonad :: [Definition] -> InferM [Sort]
checkInMonad defns = do
    -- create maps (using firsts)
    refs <- mapM (\(n,_,_) -> freshRef >>= (\r -> insertVar n r >> return r)) defns

    -- do type inference
    ps <- mapM checkDef defns
    sequence (zipWith (unify.Ref) refs ps)
    mapM (deepGet.Ref) refs

deepGet :: PartialSort -> InferM Sort
deepGet (Ref r) = do
    p <- getRef r
    case p of
        (Ref s) -> throwError "Not a specific type"
        other -> deepGet other
deepGet (ArrowP p q) = do
    s <- deepGet p
    t <- deepGet q
    return $ Arrow s t
deepGet IntP = return Int
deepGet BoolP = return Bool


deepGet' :: PartialSort -> InferM PartialSort
deepGet' (Ref r) = do
    p <- getRef r
    case p of
        (Ref s) -> return $ Ref s
        other -> deepGet' other
deepGet' (ArrowP p q) = do
    s <- deepGet' p
    t <- deepGet' q
    return $ ArrowP s t
deepGet' IntP = return IntP
deepGet' BoolP = return BoolP

checkDef :: Definition -> InferM PartialSort
checkDef (n,[],body) = inferType body
checkDef (n,arg:args,body) = do
    (p,r) <- withVariable arg (checkDef (n,args,body))
    return (ArrowP (Ref r) p)

withVariable :: Variable -> InferM a -> InferM (a,Ref)
withVariable v action = do
    r <- freshRef
    m <- gets varMap --
    insertVar v r
    --oldRef <- insertAndLookupVar v r

    x <- action
    modify (\e-> e{varMap = m})-- could just delete variable here and replace with oldRef, but this seems more efficient
    -- (and equivalent, assuming this is the only function used to modify varMap)
    return (x,r)


insertAndLookupVar :: Variable -> Ref -> InferM (Maybe Ref)
insertAndLookupVar v r = do
    m <- gets varMap
    let (oldRef,m') = M.insertLookupWithKey (const$const$const r) v r m
    modify (\e-> e{varMap = m'})
    return oldRef

type Ref = Int
data PartialSort = IntP | BoolP | Ref Ref | ArrowP PartialSort PartialSort deriving (Eq,Show)

fromSort :: Sort -> PartialSort
fromSort Int = IntP
fromSort Bool = BoolP
fromSort (Arrow a b) = ArrowP (fromSort a) (fromSort b)

data PartialEnv = PartialEnv {
    varMap :: M.Map Variable Ref,
    refMap :: M.Map Ref PartialSort}

type InferM  = StateT PartialEnv (Either String)

inferType :: Term -> InferM PartialSort
inferType (Constant c) = lift (fromSort <$> getSort c mainEnv)
inferType (Variable x) = do
    r' <- lookupVar x
    r <- case r' of
        Just r -> return r
        Nothing -> throwError ("Unknown variable: "++x)
    getRef r
inferType app@(Apply a b) = do
    t1 <- inferType a
    t2 <- inferType b
    case t1 of
        ArrowP p1 p2 -> unify t2 p1 >> return p2 -- add errorPart to give more helpful type errors
        Ref r -> do
            p2 <- freshRef
            insertRef r (ArrowP t2 (Ref p2))
            return (Ref p2)
        BoolP -> throwError ("bad type (attempting to apply boolean)\n"++show app)
        IntP -> throwError ("bad type (attempting to apply integer)\n"++show app)
inferType (If cond thn els) = do
    t1 <- inferType thn
    t2 <- inferType els
    unify t1 t2
    t3 <- inferType cond
    unify t3 BoolP
    return t2

getRef :: Ref -> InferM PartialSort
getRef r = do
    m <- gets refMap
    case M.lookup r m of
        Just p@(Ref s) -> if s==r then return p else do
            p'<-getRef s
            if p==p' then return () else insertRef r p'
            return p'
        Just p -> (return p)
        Nothing -> throwError "Ref Not found"

unify :: PartialSort -> PartialSort -> InferM ()
unify (Ref r) t = do
    p <- getRef r
    q <- get1 t --necessary to make sure that `notIn` only fails when we want it to
    if p == Ref r
        then if p == q then return () else do
            b <- r `notIn` q
            if b then insertRef r q else throwError "unable to unify (Infinite type)"
        else unify p q
unify t (Ref r) = unify (Ref r) t
unify (ArrowP t1 t2) (ArrowP s1 s2) = unify t1 s1 >> unify t2 s2
unify IntP IntP = return ()
unify BoolP BoolP = return ()
unify t1 t2 = throwError ("unable to unify "++show t1++" and "++show t2)

get1 :: PartialSort -> InferM PartialSort
get1 (Ref r) = getRef r
get1 x = return x


--assumes getRef r == Ref r
notIn :: Ref -> PartialSort -> InferM Bool
notIn r (Ref s) = do
    p <- getRef s
    case p of
        Ref t -> if r == t then return False else return True
        x -> r `notIn` x
notIn r (ArrowP x y) = do
    b <- r `notIn` x
    if b then r `notIn` y else return False
notIn r BoolP = return True
notIn r IntP = return True


lookupVar :: Variable -> InferM (Maybe Ref)
lookupVar x = M.lookup x <$> varMap <$> get

lookupRef :: Ref -> InferM PartialSort
lookupRef r = M.findWithDefault (Ref r) r <$> refMap <$> get

insertVar :: Variable -> Ref -> InferM ()
insertVar v r = do
    m <- gets varMap
    modify (\e-> e{varMap = M.insert v r m})


insertRef :: Ref -> PartialSort -> InferM ()
insertRef r s = do
    m <- gets refMap
    modify (\e-> e{refMap = (M.insert r s m)})

freshRef :: InferM Ref
freshRef = do
    r <- M.size <$> refMap <$> get
    insertRef r (Ref r)
    return r





-- Gets the sort of a constant, may be given a hint
getSort :: String -> DeltaEnv -> Either String Sort
getSort s env
    | all (`elem` ['0'..'9']) s = Right Int
    | otherwise = case lookup s env of
                          Just t -> Right t
                          Nothing -> Left ("unknown constant: "++s)--could assume here that s is a constraint


isRelational :: Sort -> Bool
isRelational Bool = True
isRelational (Arrow Int rho) = isRelational rho
isRelational (Arrow r1 r2) = isRelational r1 && isRelational r2
isRelational _ = False



--Checks that a term is well sorted in a given environment
checkSort :: DeltaEnv -> Term -> Either String ()
checkSort env t = getsort' (env++ilaEnv) Nothing t >> Right ()

getsort :: Term -> Either String Sort
getsort = getsort' ilaEnv Nothing

getsort' :: DeltaEnv -> Maybe Sort -> Term -> Either String Sort
getsort' env _ (Apply a b) = do
    sb <- getsort' env Nothing b
    sa <- getsort' env (Just sb) a
    case sa of
         Arrow s1 s2 -> if s1==sb then Right s2
                                  else Left ("type error: applying " ++ printt a ++ ":" ++ prints sa ++
                                  "\nto" ++ printt b ++ ":" ++ prints sb)
         _ -> Left ("applying non-function: "++printt a)
getsort' env _ (Lambda x s a) = do
    sa <- getsort' ((x,s):env) Nothing a
    return (Arrow s sa)
getsort' env _ (Variable x) = case lookup x env of
                                   Nothing -> Left ("unknown variable:"++x)
                                   Just s -> Right s
getsort' env hint (Constant c) =  getSort c env
