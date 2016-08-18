module Inference
    where

import DataTypes
import Parser

(%) :: String -> [String] -> String

(%) s [] = s
(%) ('{':'}':s) (x:xs) = x++(s%xs)
(%) (c:s) xs = c:(s%xs)


ilaGamma :: Gamma
ilaGamma = 
    (zip ilaOps $ repeat ([],(ArrowT "_" IntT (ArrowT "_" IntT IntT))))
  ++ map (\ r -> (r,([],ArrowT "_" IntT . ArrowT "_" IntT $ BoolT (qp ("x {}y"%[r]))))) ilaRels
  ++ map (\ r -> (r,
            ([("X",Bool),("Y",Bool)],ArrowT "_" (BoolT (qp "X")) . ArrowT "_" (BoolT (qp "Y")) $ BoolT (qp ("X "++r++"Y")))))
         logicalBinary
  ++ map (\ r -> (r,
            ([("X",Bool)],ArrowT "_" (BoolT (qp "X")) $ BoolT (qp (r++"Y")))))
         logicalUnary
  ++ [("∃", ([("X",Arrow Int Bool)],
    ArrowT "_" (ArrowT "x" IntT (BoolT $ qp "X x") ) (BoolT $ qp "∃x:int.X x")))]
