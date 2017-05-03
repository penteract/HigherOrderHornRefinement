module FormulaChecks
    where

import DataTypes
import Control.Monad.Except

-- gets the sort of a constant, may be given a hint
getSort :: String -> Maybe Sort -> DeltaEnv -> Either String Sort
getSort "∀" (Just (Arrow sigma Bool)) env = Right $ Arrow (Arrow sigma Bool) Bool
getSort "∀" _ env =  Left "body of quantifier should be boolean"
getSort "∃" (Just (Arrow sigma Bool)) env = Right $ Arrow (Arrow sigma Bool) Bool
getSort "∃" _ env =  Left "body of quantifier should be boolean"
getSort s hint env = case lookup s env of
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
getsort' env hint (Constant c) =  getSort c hint env


{-
isInt :: Term -> Bool
isInt (Apply (Apply (Constant c) a) b)
    | c `elem` ilaOps = isInt a && isInt b
isInt (Variable v) = True
isInt (Constant c)
    | c `elem` ilaConstants = True
isInt _ = False
    

isIla :: Term -> Bool
isIla (Apply (Constant c) a)
    | c `elem` logicalUnary = isIla a
isIla (Apply (Apply (Constant c) a) b)
    | c `elem` logicalBinary = isIla a && isIla b
    | c `elem` ilaRels = isInt a && isInt b
isIla _ = False

isGoal :: Term -> Maybe String --Nothing means goal, string is error
isGoal = error ""
-}
