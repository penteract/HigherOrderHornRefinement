{-# LANGUAGE FlexibleContexts #-}
module Tools((%),errorPart,fromRight,xor)
    where
import Control.Monad.Except

-- helper function for making strings nicely
(%) :: String -> [String] -> String
(%) s [] = s
(%) ('{':'}':s) (x:xs) = x++(s%xs)
(%) ('\\':c:s) xs = c:(s%xs)
(%) (c:s) xs = c:(s%xs)
(%) "" _ = error "not enough '{}' in string"

errorPart :: MonadError String m => String -> m a -> m a
errorPart s = (`catchError` (\ e ->throwError ("{} Error:\n{}" % [s,e])))

check :: Bool -> String -> Either String ()
check cond err = if cond then Right () else Left err


fromRight :: Either a b -> b
fromRight (Right x) = x


xor True x = not x
xor False x = x
