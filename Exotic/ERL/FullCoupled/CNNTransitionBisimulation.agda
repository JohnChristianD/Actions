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

record CNNKernelBisimulation (C A : Set) : Set₁ where
  constructor cnnKernelBisimulation
  field
    witness : TransitionWitness C A
    related : C → C → Set
    related-is-decode-equality : ∀ x y → related x y → CNNEquivalent witness x y
    step-closed : ∀ x y → related x y → related (cnnStep witness x) (cnnStep witness y)
open CNNKernelBisimulation public

kernel-relation : ∀ {C A} (B : CNNKernelBisimulation C A) → C → C → Set
kernel-relation B = related B

kernel-relation-preserved : ∀ {C A} (B : CNNKernelBisimulation C A)
  (x y : C) → kernel-relation B x y →
  kernel-relation B (cnnStep (witness B) x) (cnnStep (witness B) y)
kernel-relation-preserved B x y r = step-closed B x y r

kernel-iterate-preserved : ∀ {C A} (B : CNNKernelBisimulation C A)
  (n : Nat) (x y : C) → kernel-relation B x y →
  kernel-relation B (iterateCNN (witness B) n x) (iterateCNN (witness B) n y)
kernel-iterate-preserved B zero x y r = r
kernel-iterate-preserved B (suc n) x y r =
  kernel-iterate-preserved B n
    (cnnStep (witness B) x)
    (cnnStep (witness B) y)
    (step-closed B x y r)

kernel-decodes-identically : ∀ {C A} (B : CNNKernelBisimulation C A)
  (x y : C) → kernel-relation B x y →
  decode (witness B) x ≡ decode (witness B) y
kernel-decodes-identically B x y r =
  related-is-decode-equality B x y r

kernel-bisimulation-learner-invariant : ∀ {C A} (B : CNNKernelBisimulation C A)
  (n : Nat) (x y : C) → kernel-relation B x y →
  decode (witness B) (iterateCNN (witness B) n x) ≡
  decode (witness B) (iterateCNN (witness B) n y)
kernel-bisimulation-learner-invariant B n x y r =
  iterate-preserves-equivalence (witness B) n
    (related-is-decode-equality B x y (kernel-iterate-preserved B n x y r))
