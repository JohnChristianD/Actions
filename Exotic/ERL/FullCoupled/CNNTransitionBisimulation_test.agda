{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CNNTransitionBisimulation_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≡_)
open import Exotic.ERL.FullCoupled.CNNTransitionBisimulation

identityTransition : TransitionWitness Nat Nat
identityTransition = transitionWitness
  (λ x → x)
  suc
  suc
  (λ c → refl)

identityBisimulation : ∀ n {x y : Nat} →
  CNNEquivalent identityTransition x y →
  decode identityTransition (iterateCNN identityTransition n x) ≡
  decode identityTransition (iterateCNN identityTransition n y)
identityBisimulation n eq = iterate-preserves-equivalence identityTransition n eq
