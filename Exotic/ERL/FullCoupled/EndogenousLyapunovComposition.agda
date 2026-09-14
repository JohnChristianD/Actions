{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EndogenousLyapunovComposition where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.EndogenousBoundaryComposition using
  ( F4Arithmetic
  ; EndogenousF4State
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( LyapunovCertificate
  ; OrbitNonFixed
  ; noNontrivialFiniteCycle
  )

------------------------------------------------------------------------
-- Deterministic endogenous stability composition.
-- The state transition is explicit. The theorem therefore applies to a
-- deterministic learner special case only; it does not manufacture a
-- stochastic Markov kernel or an exploration process.
------------------------------------------------------------------------

record DeterministicEndogenousStability (A : F4Arithmetic) : Set₁ where
  constructor deterministicEndogenousStability
  field
    step : EndogenousF4State A → EndogenousF4State A
    lyapunov : LyapunovCertificate (EndogenousF4State A) step

open DeterministicEndogenousStability public

endogenous-no-nontrivial-cycle :
  ∀ {A : F4Arithmetic}
  (C : DeterministicEndogenousStability A)
  {s : EndogenousF4State A} (n : Nat) →
  step C s ≡ step C s →
  OrbitNonFixed (step C s) →
  ⊥
endogenous-no-nontrivial-cycle C n _ nf =
  noNontrivialFiniteCycle
    (lyapunov C)
    n
    refl
    nf
