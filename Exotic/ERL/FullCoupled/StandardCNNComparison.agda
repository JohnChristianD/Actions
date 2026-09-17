{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.StandardCNNComparison where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import Exotic.ERL.FullCoupled.ExternalCNNTransitionBisimulation as E

record FiniteDepthMachine (X Y : Set) : Set where
  constructor finiteDepthMachine
  field layer : X → Y
open FiniteDepthMachine public

record TranslationAction (X : Set) : Set where
  constructor translationAction
  field shift : Nat → X → X
open TranslationAction public

record ConvolutionalMachine (X R : Set) : Set where
  constructor convolutionalMachine
  field
    encode : X → R
    translation : TranslationAction X

record ConvolutionalEquivariance (X R : Set)
  (C : ConvolutionalMachine X R) : Set where
  constructor convolutionalEquivariance
  field
    featureShift : ∀ n x →
      encode C (shift (translation C) n x) ≡
      encode C x

record CNNTransitionClass (X R H S : Set) : Set where
  constructor cnnTransitionClass
  field
    cnn : ConvolutionalMachine X R
    adapter : E.RepresentationAdapter R H
    transition : E.LearnerTransition H S
    nextState : S → S
    depthMachine : Nat → FiniteDepthMachine X R
    depthAgreement : ∀ n x →
      layer (depthMachine n) x ≡ encode cnn x
    equivariance : ConvolutionalEquivariance X R cnn

cnnDepthFactorization : ∀ {X R H S : Set}
  (C : CNNTransitionClass X R H S) n x →
  E.CNNEquivalent (cnn C) (adapter C) x x
cnnDepthFactorization C n x =
  refl

cnnTransitionStep : ∀ {X R H S : Set}
  (C : CNNTransitionClass X R H S) n x y →
  E.CNNEquivalent (cnn C) (adapter C) x y →
  E.CNNEquivalent (cnn C) (adapter C)
    (shift (translation (cnn C)) n x)
    (shift (translation (cnn C)) n y)
cnnTransitionStep C n x y e =
  trans
    (cong (E.RepresentationAdapter.decode (adapter C)) e)
    refl

standardCNNComparison : ∀ {X R H S : Set}
  (C : CNNTransitionClass X R H S) n x y →
  E.CNNEquivalent (cnn C) (adapter C) x y →
  E.CNNEquivalent (cnn C) (adapter C)
    (shift (translation (cnn C)) n x)
    (shift (translation (cnn C)) n y)
standardCNNComparison C n x y e =
  cnnTransitionStep C n x y e

cnnMachineTransitionPreserves : ∀ {X R H S : Set}
  (C : CNNTransitionClass X R H S) n x y →
  E.CNNEquivalent (cnn C) (adapter C) x y →
  transition C (
    E.RepresentationAdapter.decode (adapter C)
      (encode (cnn C) x)) ≡
  transition C (
    E.RepresentationAdapter.decode (adapter C)
      (encode (cnn C) y))
cnnMachineTransitionPreserves C n x y e =
  cong (transition C) (cong (E.RepresentationAdapter.decode (adapter C)) e)

cnnNextPreserves : ∀ {X R H S : Set}
  (C : CNNTransitionClass X R H S) n x y →
  E.CNNEquivalent (cnn C) (adapter C) x y →
  nextState C
    (transition C (E.RepresentationAdapter.decode (adapter C) (encode (cnn C) x))) ≡
  nextState C
    (transition C (E.RepresentationAdapter.decode (adapter C) (encode (cnn C) y)))
cnnNextPreserves C n x y e =
  cong (nextState C) (cnnMachineTransitionPreserves C n x y e)

-- This module contains only the comparison class and its preservation laws.
-- It does not define a convolution kernel, stride, padding rule, tensor layout,
-- trained weights, or a CNN implementation. Those remain external instantiations.
