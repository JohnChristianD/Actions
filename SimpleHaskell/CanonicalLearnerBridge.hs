{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
module SimpleHaskell.CanonicalLearnerBridge where

import Language.Haskell.Liquid.ProofCombinators (Proof, trivial)

-- Provenance: FullCoupled/CanonicalLearnerMonolith.agda

{-@ identityActivation8 :: x:Int -> {v:Int | v = x} @-}
identityActivation8 :: Int -> Int
identityActivation8 x = x

{-@ identityActivation8Injective :: x:Int -> y:Int
      -> { identityActivation8 x == identityActivation8 y ==> x == y } @-}
identityActivation8Injective :: Int -> Int -> Proof
identityActivation8Injective _ _ = trivial

{-@ natPlusZero :: n:{Int | n >= 0} -> { n + 0 == n } @-}
natPlusZero :: Int -> Proof
natPlusZero _ = trivial

{-@ natScaleStep :: n:{Int | n >= 0} -> k:{Int | k >= 0}
      -> { (n + 1) * k == n * k + k } @-}
natScaleStep :: Int -> Int -> Proof
natScaleStep _ _ = trivial
