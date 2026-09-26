{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Impossibility boundary for naive arbitrary-limit closure.
--
-- A convergence/approximation interface without a surviving separating
-- decoder cannot, by itself, imply injectivity of the limit representation.
-- The countermodel below is deliberately finite: Bool is collapsed to Unit.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.GRUFractalLimitConvergenceImpossibility where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

false-not-true : ¬ (false ≡ true)
false-not-true ()

constant-limit : Bool → ⊤
constant-limit _ = tt

trivial-convergence :
  ∀ state →
  ⊤
trivial-convergence _ = tt

------------------------------------------------------------------------
-- There cannot be a generic theorem that turns an arbitrary supplied
-- "convergence witness" into limit injectivity.  The premises below are
-- intentionally no stronger than a total witness for every state.
------------------------------------------------------------------------

naive-limit-injectivity-impossible :
  ¬
  (∀ {State LimitObservation : Set}
    (limitEncode : State → LimitObservation) →
    (∀ state → ⊤) →
    ∀ {s t : State} →
    limitEncode s ≡ limitEncode t →
    s ≡ t)
naive-limit-injectivity-impossible derive =
  false-not-true
    (derive constant-limit trivial-convergence
      {s = false} {t = true} refl)

------------------------------------------------------------------------
-- Interpretation:
--
--   approximation/convergence witness alone
--              ↛
--        limit injectivity
--
-- A separate separation mechanism is necessary.  The repository's
-- limit-left-inverse kernel supplies exactly that missing mechanism.
------------------------------------------------------------------------
