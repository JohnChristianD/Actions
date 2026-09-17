{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusTraceSemidirect where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

record MobiusTrace : Set where
  constructor mobiusTrace
  field
    atDepth : Nat → L.MobiusAction
open MobiusTrace public

identityMobius : L.MobiusAction
identityMobius = L.mobiusAction (λ x → x)

prefixAction : MobiusTrace → Nat → L.MobiusAction
prefixAction T zero = identityMobius
prefixAction T (suc n) =
  L.composeMobius (atDepth T n) (prefixAction T n)

prefixAction-law : ∀ T n x →
  L.run (prefixAction T (suc n)) x ≡
  L.run (atDepth T n) (L.run (prefixAction T n) x)
prefixAction-law T n x = refl

traceInput : MobiusTrace → Nat → L.Int8 → L.Int8
traceInput T n x = L.run (prefixAction T n) x

traceGRUStep : MobiusTrace → Nat → L.GRUState → L.Int8 → L.GRUState
traceGRUStep T n s x = L.gruStep s (traceInput T n x)

traceGRU : MobiusTrace → Nat → L.GRUState → L.Int8 → L.GRUState
traceGRU T zero s x = s
traceGRU T (suc n) s x =
  L.gruStep (traceGRU T n s x) (traceInput T n x)

traceGRU-step-law : ∀ T n s x →
  traceGRU T (suc n) s x ≡
  L.gruStep (traceGRU T n s x)
    (L.run (atDepth T n) (traceInput T n x))
traceGRU-step-law T n s x =
  cong (λ u → L.gruStep (traceGRU T n s x) u)
    (prefixAction-law T n x)

semidirectMobiusStep : L.MobiusAction → L.GRUState → L.Int8 → L.GRUState
semidirectMobiusStep m s x = L.gruStep s (L.run m x)

semidirect-product-law : ∀ f g s x →
  semidirectMobiusStep (L.composeMobius f g) s x ≡
  semidirectMobiusStep f s (L.run g x)
semidirect-product-law f g s x = refl

trace-prefix-semidirect : ∀ T n s x →
  traceGRUStep T n s x ≡
  semidirectMobiusStep (prefixAction T n) s x
trace-prefix-semidirect T n s x = refl

trace-gru-prefix-law : ∀ T n s x →
  traceGRUStep T (suc n) s x ≡
  L.gruStep (traceGRU T n s x)
    (L.run (atDepth T n) (traceInput T n x))
trace-gru-prefix-law = traceGRU-step-law

trace-depth-invariant : ∀ T n s x →
  L.gruPersistent (traceGRU T n s x) ≡
  L.gruPersistent s
trace-depth-invariant T zero s x = refl
trace-depth-invariant T (suc n) s x =
  trans
    (L.gruPersistentLaw (traceGRU T n s x) (traceInput T n x))
    (trace-depth-invariant T n s x)
