module Tools
    where

-- helper function for making strings nicely
(%) :: String -> [String] -> String
(%) s [] = s
(%) ('{':'}':s) (x:xs) = x++(s%xs)
(%) ('\\':c:s) xs = c:(s%xs)
(%) (c:s) xs = c:(s%xs)
(%) "" _ = error "not enough '{}' in string"

errorPart :: String -> Either String a -> Either String a
errorPart s (Left x)= Left ("{} Error:\n{}" % [s,x])
errorPart _ (Right x) = Right x

check :: Bool -> String -> Either String ()
check cond err = if cond then Right () else Left err

unless = flip check

infixl 1 `unless`

fromRight :: Either a b -> b
fromRight (Right x) = x