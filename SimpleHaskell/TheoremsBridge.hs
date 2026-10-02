{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
module SimpleHaskell.TheoremsBridge where

-- Provenance:
--   FullCoupled/TheoremsMonolith.agda
-- These are independent SMT checks of algebraic/proof-boundary claims
-- already present in the Agda theorem surface.

{-@ integerAssociativity :: x:Int -> y:Int -> z:Int
      -> {v:() | x + (y + z) == (x + y) + z} @-}
integerAssociativity :: Int -> Int -> Int -> ()
integerAssociativity _ _ _ = ()

{-@ natAssociativity :: x:{Int | x >= 0} -> y:{Int | y >= 0} -> z:{Int | z >= 0}
      -> {v:() | x + (y + z) == (x + y) + z} @-}
natAssociativity :: Int -> Int -> Int -> ()
natAssociativity _ _ _ = ()

{-@ integerMultiplyDistributive :: x:Int -> y:Int -> z:Int
      -> {v:() | x * (y + z) == x * y + x * z} @-}
integerMultiplyDistributive :: Int -> Int -> Int -> ()
integerMultiplyDistributive _ _ _ = ()

{-@ listLengthAppend :: xs:[a] -> ys:[a]
      -> {v:() | len (xs ++ ys) == len xs + len ys} @-}
listLengthAppend :: [a] -> [a] -> ()
listLengthAppend _ _ = ()
