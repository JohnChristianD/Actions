{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ExternalCNNTransitionBisimulationStrong where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)

record ExternalCNN (X R : Set) : Set where
  constructor externalCNN
  field encode : X → R
open ExternalCNN public

record RepresentationAdapter (R H : Set) : Set where
  constructor representationAdapter
  field decode : R → H
open RepresentationAdapter public

record LearnerTransition (H S : Set) : Set where
  constructor learnerTransition
  field input : H → S
open LearnerTransition public

CNNEquivalent : ∀ {X R H : Set} → ExternalCNN X R → RepresentationAdapter R H → X → X → Set
CNNEquivalent C D x y = decode D (encode C x) ≡ decode D (encode C y)

record CNNTransitionClass (X R H S : Set) : Set where
  constructor cnnTransitionClass
  field
    cnn : ExternalCNN X R
    adapter : RepresentationAdapter R H
    transition : LearnerTransition H S
    next : S → S
open CNNTransitionClass public

stepMap : ∀ {X R H S : Set} → CNNTransitionClass X R H S → X → S
stepMap W x = next W (input (transition W) (decode (adapter W) (encode (cnn W) x)))

step-preserves :
  ∀ {X R H S : Set} (W : CNNTransitionClass X R H S) {x y : X} →
  CNNEquivalent (cnn W) (adapter W) x y →
  stepMap W x ≡ stepMap W y
step-preserves W e = cong (next W) (cong (input (transition W)) e)

iterateStepMap : ∀ {X R H S : Set} → Nat → CNNTransitionClass X R H S → X → S → S
iterateStepMap zero W x s = s
iterateStepMap (suc n) W x s = iterateStepMap n W x (stepMap W x)

iterate-preserves :
  ∀ {X R H S : Set} (W : CNNTransitionClass X R H S) {x y : X}
  (e : CNNEquivalent (cnn W) (adapter W) x y) n s →
  iterateStepMap n W x s ≡ iterateStepMap n W y s
iterate-preserves W e zero s = refl
iterate-preserves W e (suc n) s =
  trans
    (iterate-preserves W e n (stepMap W x))
    (cong (λ z → iterateStepMap n W y z) (step-preserves W e))

same-class-next-preserves :
  ∀ {X R H S : Set} (W : CNNTransitionClass X R H S) {x y : X} →
  CNNEquivalent (cnn W) (adapter W) x y →
  stepMap W x ≡ stepMap W y
same-class-next-preserves = step-preserves

cnn-factorization :
  ∀ {X R H S : Set} (W : CNNTransitionClass X R H S) x →
  stepMap W x ≡ next W (input (transition W) (decode (adapter W) (encode (cnn W) x)))
cnn-factorization W x = refl

cnn-architecture-independence :
  ∀ {X R H S : Set}
  (C : ExternalCNN X R)
  (A : RepresentationAdapter R H)
  (T : LearnerTransition H S)
  (N : S → S) x y →
  decode A (encode C x) ≡ decode A (encode C y) →
  N (input T (decode A (encode C x))) ≡ N (input T (decode A (encode C y)))
cnn-architecture-independence C A T N x y e = cong N (cong (input T) e)
