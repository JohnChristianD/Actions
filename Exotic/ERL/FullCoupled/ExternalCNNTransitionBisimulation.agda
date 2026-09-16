{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ExternalCNNTransitionBisimulation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

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

record TransitionBisimulation (X S : Set) : Set where
  constructor transitionBisimulation
  field relation : X → X → Set
        observe : X → S
open TransitionBisimulation public

externalCNN-transition-preserves :
  ∀ {X R H S : Set}
  (C : ExternalCNN X R)
  (D : RepresentationAdapter R H)
  (T : LearnerTransition H S)
  (x y : X) →
  CNNEquivalent C D x y →
  input T (decode D (encode C x)) ≡ input T (decode D (encode C y))
externalCNN-transition-preserves C D T x y e = cong (input T) e

record CNNBisimulationWitness (X R H S : Set) : Set where
  constructor cnnBisimulationWitness
  field
    cnn : ExternalCNN X R
    adapter : RepresentationAdapter R H
    transition : LearnerTransition H S
    next : S → S

cnn-bisimulation-step :
  ∀ {X R H S : Set}
  (W : CNNBisimulationWitness X R H S)
  {x y : X} →
  CNNEquivalent (cnn W) (adapter W) x y →
  next W (input (transition W) (decode (adapter W) (encode (cnn W) x)))
    ≡
  next W (input (transition W) (decode (adapter W) (encode (cnn W) y)))
cnn-bisimulation-step W e =
  cong (next W) (externalCNN-transition-preserves
    (cnn W) (adapter W) (transition W) _ _ e)

cnn-class-lift :
  ∀ {X R H S : Set}
  (C : ExternalCNN X R)
  (D : RepresentationAdapter R H)
  (T : LearnerTransition H S)
  (N : S → S) →
  X → S
cnn-class-lift C D T N x = N (input T (decode D (encode C x)))

cnn-class-lift-factorization :
  ∀ {X R H S : Set}
  (C : ExternalCNN X R)
  (D : RepresentationAdapter R H)
  (T : LearnerTransition H S)
  (N : S → S) x →
  cnn-class-lift C D T N x ≡ N (input T (decode D (encode C x)))
cnn-class-lift-factorization C D T N x = refl
