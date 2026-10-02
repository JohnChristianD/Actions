{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
module SimpleHaskell.CanonicalLearnerBridge where

-- Provenance:
--   FullCoupled/CanonicalLearnerMonolith.agda
-- The executable interface is deliberately Simple Haskell.  LiquidHaskell
-- re-proves selected erased algebraic/refinement surfaces with Z3.

{-@ identityActivation8 :: x:Int -> {v:Int | v = x} @-}
identityActivation8 :: Int -> Int
identityActivation8 x = x

{-@ identityActivation8Injective :: x:Int -> y:Int
      -> {v:() | identityActivation8 x == identityActivation8 y ==> x == y} @-}
identityActivation8Injective :: Int -> Int -> ()
identityActivation8Injective _ _ = ()

{-@ natPlusZero :: n:{Int | n >= 0} -> {v:() | n + 0 == n} @-}
natPlusZero :: Int -> ()
natPlusZero _ = ()

{-@ natScaleStep :: n:{Int | n >= 0} -> k:{Int | k >= 0}
      -> {v:() | (n + 1) * k == n * k + k} @-}
natScaleStep :: Int -> Int -> ()
natScaleStep _ _ = ()
