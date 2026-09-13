{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalExecutable where

open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (toℕ)
open import Exotic.efficient_chad.Int8 using (code; one8; zero8)
open import Exotic.ERL.Exploration.FiniteNoise using (zero)
open import Exotic.ERL.FullCoupled.FiniteLearner using (token)
open import Exotic.ERL.FullCoupled.CanonicalLearner

------------------------------------------------------------------------
-- This is an executable projection of the canonical Agda definition. It does
-- not reimplement the learner: the generated Haskell calls the same `step`.
------------------------------------------------------------------------

witness : Nat
witness =
  toℕ
    (code
      (q
        (xi
          (step start zero zero
            (token one8 zero8 one8 zero8)
            (token zero8 zero8 zero8 zero8)
            one8))))
