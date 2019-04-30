{-# LANGUAGE FlexibleContexts,FlexibleInstances #-}

{-
Some functions that are used across the program
-}


module HOCHC.Utils((%),errorPart,fromRight,xor,(>><),check,(?),throwError)
    where
import Control.Monad.Except
import qualified Control.Monad.Fail

instance Control.Monad.Fail.MonadFail (Either String) where
    fail s = Left s

-- helper function for constructing strings nicely
(%) :: String -> [String] -> String
(%) s [] = s
(%) ('{':'}':s) (x:xs) = x++(s%xs)
(%) ('\\':c:s) xs = c:(s%xs)
(%) (c:s) xs = c:(s%xs)
(%) "" _ = error "not enough '{}' in string"

-- Annotates errors that originate from a region of code
errorPart :: MonadError String m => String -> m a -> m a
errorPart s = (`catchError` (\ e ->throwError ("{} Error:\n{}" % [s,e])))


(?) :: MonadError e m => Maybe a -> e -> m a
(?) = flip$ (`maybe` return) .throwError
--(?) m e = maybe (throwError e) return m

check :: MonadError String m => Bool -> String -> m ()
check cond err = if cond then return () else throwError err

fromRight :: Either a b -> b
fromRight (Right x) = x

(>><) :: Monad m => m a -> (a-> m b) -> m a
xm >>< f = xm >>= (\x -> f x >> return x)

xor True x = not x
xor False x = x
