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

standardMunchausenScaleCode8 : Int8
standardMunchausenScaleCode8 = int8OfNat 16

negativeMunchausenScaleCode8 : Int8
negativeMunchausenScaleCode8 = lcbNegate standardMunchausenScaleCode8

negativeMunchausenScaleCode8-law :
  code negativeMunchausenScaleCode8 ≡ fromℕ< (m%n<n 240 256)
negativeMunchausenScaleCode8-law = refl

negativeMunchausenScaleCode8-cancels-standard :
  int8Add standardMunchausenScaleCode8 negativeMunchausenScaleCode8 ≡ zero8
negativeMunchausenScaleCode8-cancels-standard = refl

record PolicyQLog8 : Set where
  constructor policyQLog8
  field
    source : Int8
    finiteValue : FiniteRational
open PolicyQLog8 public

policyQLog8-value : ∀ logPi →
  finiteValue (policyQLog8 logPi (finiteQLog8 logPi)) ≡ finiteQLog8 logPi
policyQLog8-value logPi = refl

finiteMaxEntQLog8 : Int8 → FiniteRational
finiteMaxEntQLog8 = finiteQLog8

finiteMaxEntQLog8-identical : ∀ x →
  finiteMaxEntQLog8 x ≡ finiteQLog8 x
finiteMaxEntQLog8-identical x = refl

finiteMaxEntQLog8-transcendental-free : ∀ x →
  finiteMaxEntQLog8 x ≡ finiteRational
    (rationalSign (finiteMaxEntQLog8 x))
    (rationalNumerator (finiteMaxEntQLog8 x))
    (rationalDenominator (finiteMaxEntQLog8 x))
finiteMaxEntQLog8-transcendental-free x = refl

data MunchausenRewardTerm : Set where
  baseReward : Int8 → MunchausenRewardTerm
  policyQLog : PolicyQLog8 → MunchausenRewardTerm
  scaleBy : SignedFiniteScale → MunchausenRewardTerm → MunchausenRewardTerm
  addTerm : MunchausenRewardTerm → MunchausenRewardTerm → MunchausenRewardTerm

munchausenShapedReward : Int8 → SignedFiniteScale → Int8 → MunchausenRewardTerm
munchausenShapedReward reward α logPi =
  addTerm (baseReward reward)
    (scaleBy α (policyQLog (policyQLog8 logPi (finiteMaxEntQLog8 logPi))))

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

negativeMunchausen-keeps-qLog : ∀ reward magnitude logPi →
  finiteValue (policyQLog8 logPi (finiteMaxEntQLog8 logPi)) ≡ finiteMaxEntQLog8 logPi
negativeMunchausen-keeps-qLog reward magnitude logPi = refl

standardMunchausenBonus8 : Int8 → Int8
standardMunchausenBonus8 logPi =
  int8Mul standardMunchausenScaleCode8
    (rationalCode (finiteMaxEntQLog8 logPi))

negativeMunchausenBonus8 : Int8 → Int8
negativeMunchausenBonus8 logPi =
  int8Mul negativeMunchausenScaleCode8
    (rationalCode (finiteMaxEntQLog8 logPi))

negativeMunchausenBonus8-law : ∀ logPi →
  negativeMunchausenBonus8 logPi ≡
  int8Mul (lcbNegate standardMunchausenScaleCode8)
    (rationalCode (finiteMaxEntQLog8 logPi))
negativeMunchausenBonus8-law logPi = refl

negativeMunchausenReward8 : Int8 → Int8 → Int8
negativeMunchausenReward8 reward logPi =
  int8Add reward (negativeMunchausenBonus8 logPi)

negativeMunchausenReward8-law : ∀ reward logPi →
  negativeMunchausenReward8 reward logPi ≡
  int8Add reward
    (int8Mul (lcbNegate standardMunchausenScaleCode8)
      (rationalCode (finiteMaxEntQLog8 logPi)))
negativeMunchausenReward8-law reward logPi = refl

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
    logPi bootstrap

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
  scaleBy (endogenousNegativeMunchausenScale8 K s)
    (policyQLog (policyQLog8 logPi (finiteMaxEntQLog8 logPi)))

negativeMunchausenQLogTerm-law : ∀ (K : FullLearnerKernel) (s : FullLearnerState) (logPi : Int8) →
  negativeMunchausenQLogTerm K s logPi ≡
  scaleBy (endogenousNegativeMunchausenScale8 K s)
    (policyQLog (policyQLog8 logPi (finiteMaxEntQLog8 logPi)))
negativeMunchausenQLogTerm-law K s logPi = refl