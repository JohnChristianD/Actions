{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
module SimpleHaskell.TheoremsBridge where

import Language.Haskell.Liquid.ProofCombinators (Proof, trivial)

-- Provenance: FullCoupled/TheoremsMonolith.agda

{-@ integerAssociativity :: x:Int -> y:Int -> z:Int
      -> { x + (y + z) == (x + y) + z } @-}
integerAssociativity :: Int -> Int -> Int -> Proof
integerAssociativity _ _ _ = trivial

{-@ natAssociativity :: x:{Int | x >= 0} -> y:{Int | y >= 0} -> z:{Int | z >= 0}
      -> { x + (y + z) == (x + y) + z } @-}
natAssociativity :: Int -> Int -> Int -> Proof
natAssociativity _ _ _ = trivial

{-@ integerMultiplyDistributive :: x:Int -> y:Int -> z:Int
      -> { x * (y + z) == x * y + x * z } @-}
integerMultiplyDistributive :: Int -> Int -> Int -> Proof
integerMultiplyDistributive _ _ _ = trivial
