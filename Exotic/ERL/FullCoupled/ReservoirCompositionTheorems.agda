{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ReservoirCompositionTheorems where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)
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

mobius-trace-two-compose : ∀ T₀ n m s x →
  T.semidirectMobiusStep
    (L.composeMobius (L.prefixAction T₀ n) (L.prefixAction T₀ m))
    s x ≡
  L.gruStep s
    (L.run (L.prefixAction T₀ n)
      (L.run (L.prefixAction T₀ m) x))
mobius-trace-two-compose T₀ n m s x =
  T.trace-prefix-semidirect-composition T₀ n m s x
