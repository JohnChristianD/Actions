{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUCompositionAlgebra where

open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; gruStep
  )

stepAction : Int8 → GRUState → GRUState
stepAction x s = gruStep s x
