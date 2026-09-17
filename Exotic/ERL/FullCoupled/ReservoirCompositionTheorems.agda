{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ReservoirCompositionTheorems where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Nat using (Nat; suc)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T

trace-prefix-two-step : ∀ T₀ n x →
  T.traceInput T₀ (suc (suc n)) x ≡
  L.run (L.atDepth T₀ (suc n))
    (L.run (L.atDepth T₀ n) (T.traceInput T₀ n x))
trace-prefix-two-step T₀ n x =
  trans
    (T.prefixAction-law T₀ (suc n) x)
    (cong
      (λ u → L.run (L.atDepth T₀ (suc n)) u)
      (T.prefixAction-law T₀ n x))

trace-prefix-three-step : ∀ T₀ n x →
  T.traceInput T₀ (suc (suc (suc n))) x ≡
  L.run (L.atDepth T₀ (suc (suc n)))
    (L.run (L.atDepth T₀ (suc n))
      (L.run (L.atDepth T₀ n) (T.traceInput T₀ n x)))
trace-prefix-three-step T₀ n x =
  trans
    (T.prefixAction-law T₀ (suc (suc n)) x)
    (cong
      (λ u → L.run (L.atDepth T₀ (suc (suc n))) u)
      (trace-prefix-two-step T₀ n x))

trace-prefix-reassociate : ∀ T₀ n m x →
  T.traceInput T₀ (suc n) x ≡
  L.run (L.atDepth T₀ n)
    (L.run (L.prefixAction T₀ m) x)
  →
  L.run (L.atDepth T₀ (suc n))
      (T.traceInput T₀ (suc m) x)
    ≡
  L.run (L.atDepth T₀ (suc n))
      (L.run (L.atDepth T₀ m) (L.run (L.prefixAction T₀ m) x))
trace-prefix-reassociate T₀ n m x h =
  cong
    (λ u → L.run (L.atDepth T₀ (suc n)) u)
    h

mobius-trace-two-compose : ∀ T₀ n m s x →
  T.semidirectMobiusStep
    (L.composeMobius (L.prefixAction T₀ n) (L.prefixAction T₀ m))
    s x ≡
  L.gruStep s
    (L.run (L.prefixAction T₀ n)
      (L.run (L.prefixAction T₀ m) x))
mobius-trace-two-compose T₀ n m s x =
  T.trace-prefix-semidirect-composition T₀ n m s x

bounded-output-composition : ∀ {A : Nat}
  (K : L.LearnerKernel A) (s : L.LearnerState A) →
  L.toℕ (L.code
    (T.project
      (T.quotientWitness
        (λ z → z)
        (λ a b → a ≡ b)
        (λ e → e))
      s)) < 256 →
  L.toℕ (L.code (L.hiddenState (L.gru s))) < 256
bounded-output-composition K s h = h
