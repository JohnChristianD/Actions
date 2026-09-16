{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CNNTransitionBisimulation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_∸_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

record TransitionWitness (C A : Set) : Set₁ where
  constructor transitionWitness
  field
    decode : C → A
    cnnStep : C → C
    learnerStep : A → A
    commute : ∀ c → decode (cnnStep c) ≡ learnerStep (decode c)
open TransitionWitness public

CNNEquivalent : ∀ {C A} → TransitionWitness C A → C → C → Set
CNNEquivalent W x y = decode W x ≡ decode W y

cnnStep-preserves-equivalence : ∀ {C A} (W : TransitionWitness C A) {x y : C} →
  CNNEquivalent W x y → CNNEquivalent W (cnnStep W x) (cnnStep W y)
cnnStep-preserves-equivalence W eq =
  trans (commute W _) (trans (cong (learnerStep W) eq) (sym (commute W _)))

iterateCNN : ∀ {C A} (W : TransitionWitness C A) → Nat → C → C
iterateCNN W zero c = c
iterateCNN W (suc n) c = cnnStep W (iterateCNN W n c)

iterateLearner : ∀ {C A} (W : TransitionWitness C A) → Nat → A → A
iterateLearner W zero a = a
iterateLearner W (suc n) a = learnerStep W (iterateLearner W n a)

commute-iterate : ∀ {C A} (W : TransitionWitness C A) n c →
  decode W (iterateCNN W n c) ≡ iterateLearner W n (decode W c)
commute-iterate W zero c = refl
commute-iterate W (suc n) c =
  trans (commute W (iterateCNN W n c))
    (cong (learnerStep W) (commute-iterate W n c))

iterate-preserves-equivalence : ∀ {C A} (W : TransitionWitness C A) n {x y : C} →
  CNNEquivalent W x y →
  decode W (iterateCNN W n x) ≡ decode W (iterateCNN W n y)
iterate-preserves-equivalence W n eq =
  trans (commute-iterate W n _) 
    (trans (cong (iterateLearner W n) eq) (sym (commute-iterate W n _)))

record CNNBisimulationClaim (C A : Set) : Set₁ where
  constructor cnnBisimulationClaim
  field
    witness : TransitionWitness C A
open CNNBisimulationClaim public

bisimulation-claim : ∀ {C A} → CNNBisimulationClaim C A →
  ∀ n x y → CNNEquivalent (witness _) x y →
  decode (witness _) (iterateCNN (witness _) n x) ≡
  decode (witness _) (iterateCNN (witness _) n y)
bisimulation-claim B n x y eq = iterate-preserves-equivalence (witness B) n eq
