{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.FourLawClosureImpossibility where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Exotic.ERL.FullCoupled.FourLawClosureWitnesses

GenericFourLawClosureConstructor :
  Set₁
GenericFourLawClosureConstructor =
  ∀ {LearnerState PhysicalState Current Variation Action : Set}
    (Admissible : Variation → Set)
    (Stationary : PhysicalState → Set)
    (learnerStep : LearnerState → LearnerState)
    (physicalStep : PhysicalState → PhysicalState) →
    FourLawOneStepWitnessContract
      LearnerState
      PhysicalState
      Current
      Variation
      Action
      Admissible
      Stationary
      learnerStep
      physicalStep

no-generic-four-law-closure-constructor :
  GenericFourLawClosureConstructor → ⊥
no-generic-four-law-closure-constructor make =
  LawIIIVariationalWitness.stationary
    (FourLawOneStepWitnessContract.lawIII
      (make
        {LearnerState = ⊤}
        {PhysicalState = ⊤}
        {Current = ⊤}
        {Variation = ⊤}
        {Action = ⊤}
        (λ _ → ⊤)
        (λ _ → ⊥)
        (λ _ → tt)
        (λ _ → tt)))
    tt

NoGenericFourLawClosure : Set₁
NoGenericFourLawClosure = GenericFourLawClosureConstructor → ⊥
