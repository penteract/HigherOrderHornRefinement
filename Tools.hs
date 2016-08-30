module Tools
    where

(%) :: String -> [String] -> String
(%) s [] = s
(%) ('{':'}':s) (x:xs) = x++(s%xs)
(%) ('\\':c:s) xs = c:(s%xs)
(%) (c:s) xs = c:(s%xs)
(%) "" _ = error "not enough '{}' in string"

errorPart :: String -> Either String a -> Either String a
errorPart s (Left x)= Left ("{} Error:\n{}" % [s,x])
errorPart _ (Right x) = Right x