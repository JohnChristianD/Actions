{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalNegativeMunchausenTheory where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

data ScaleSign : Set where
  positiveScale negativeScale : ScaleSign

record SignedFiniteScale : Set where
  constructor signedFiniteScale
  field
    sign : ScaleSign
    magnitude : Int8
open SignedFiniteScale public

flipScale : SignedFiniteScale → SignedFiniteScale
flipScale s with sign s
... | positiveScale = signedFiniteScale negativeScale (magnitude s)
... | negativeScale = signedFiniteScale positiveScale (magnitude s)

flipScale-involutive : ∀ s → flipScale (flipScale s) ≡ s
flipScale-involutive s with sign s
... | positiveScale = refl
... | negativeScale = refl

standardMunchausenScale8 : SignedFiniteScale
standardMunchausenScale8 = signedFiniteScale positiveScale (int8OfNat 16)

negativeMunchausenScale8 : SignedFiniteScale
negativeMunchausenScale8 = flipScale standardMunchausenScale8

negativeMunchausenScale8-law :
  negativeMunchausenScale8 ≡ signedFiniteScale negativeScale (int8OfNat 16)
negativeMunchausenScale8-law = refl

data MunchausenRewardTerm : Set where
  baseReward : Int8 → MunchausenRewardTerm
  policyQLog : Int8 → MunchausenRewardTerm
  scaleBy : SignedFiniteScale → MunchausenRewardTerm → MunchausenRewardTerm
  addTerm : MunchausenRewardTerm → MunchausenRewardTerm → MunchausenRewardTerm

munchausenShapedReward : Int8 → SignedFiniteScale → Int8 → MunchausenRewardTerm
munchausenShapedReward reward α logPi =
  addTerm (baseReward reward) (scaleBy α (policyQLog logPi))

negativeMunchausenShapedReward : Int8 → Int8 → Int8 → MunchausenRewardTerm
negativeMunchausenShapedReward reward magnitude logPi =
  munchausenShapedReward reward
    (signedFiniteScale negativeScale magnitude)
    logPi

negativeMunchausen-is-sign-flipped : ∀ reward magnitude logPi →
  negativeMunchausenShapedReward reward magnitude logPi
  ≡ munchausenShapedReward reward
      (flipScale (signedFiniteScale positiveScale magnitude))
      logPi
negativeMunchausen-is-sign-flipped reward magnitude logPi = refl

record MunchausenBellmanTarget : Set where
  constructor munchausenBellmanTarget
  field
    shapedReward : MunchausenRewardTerm
    discountedBootstrap : Int8
open MunchausenBellmanTarget public

standardMunchausenTarget : Int8 → SignedFiniteScale → Int8 → Int8 → MunchausenBellmanTarget
standardMunchausenTarget reward α logPi bootstrap =
  munchausenBellmanTarget
    (munchausenShapedReward reward α logPi)
    bootstrap

negativeMunchausenTarget : Int8 → Int8 → Int8 → Int8 → MunchausenBellmanTarget
negativeMunchausenTarget reward magnitude logPi bootstrap =
  standardMunchausenTarget reward
    (signedFiniteScale negativeScale magnitude)
    logPi
    bootstrap

negativeMunchausenTarget-is-standard-flip : ∀ reward magnitude logPi bootstrap →
  negativeMunchausenTarget reward magnitude logPi bootstrap
  ≡ standardMunchausenTarget reward
      (flipScale (signedFiniteScale positiveScale magnitude))
      logPi bootstrap
negativeMunchausenTarget-is-standard-flip reward magnitude logPi bootstrap = refl

endogenousNegativeMunchausenScale8 : FullLearnerKernel → FullLearnerState → SignedFiniteScale
endogenousNegativeMunchausenScale8 K s =
  signedFiniteScale negativeScale
    (endogenousNegativeScale8 (canonicalPolicy K s))

endogenousNegativeMunchausenScale-law : ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  endogenousNegativeMunchausenScale8 K s ≡
  flipScale
    (signedFiniteScale positiveScale
      (endogenousNegativeScale8 (canonicalPolicy K s)))
endogenousNegativeMunchausenScale-law K s = refl

negativeMunchausenQLogTerm : FullLearnerKernel → FullLearnerState → Int8 → MunchausenRewardTerm
negativeMunchausenQLogTerm K s logPi =
  scaleBy (endogenousNegativeMunchausenScale8 K s) (policyQLog logPi)

negativeMunchausenQLogTerm-law : ∀ (K : FullLearnerKernel) (s : FullLearnerState) (logPi : Int8) →
  negativeMunchausenQLogTerm K s logPi ≡
  scaleBy (endogenousNegativeMunchausenScale8 K s) (policyQLog logPi)
negativeMunchausenQLogTerm-law K s logPi = refl
