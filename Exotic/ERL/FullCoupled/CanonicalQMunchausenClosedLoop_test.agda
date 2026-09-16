{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalQMunchausenClosedLoop_test where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin using (Fin)
open import Exotic.ERL.FullCoupled.CanonicalQMunchausenClosedLoop

genericClosedLoopPreservesClock : ∀ (m : MunchausenMode) (s : FullLearnerState) (a : Fin 2) (r : Int8) →
  clock (closedLoopStepMode learnerKernel m s a r) ≡ suc (clock s)
genericClosedLoopPreservesClock m s a r = refl

negativeModeIsSignFlipped :
  negativeQMunchausenScale8 ≡ signedFiniteScale one8 (int8OfNat 16)
negativeModeIsSignFlipped = refl

standardAndNegativeAreDistinctWitness :
  shapedRewardCode standardMunchausenMode one8 (int8OfNat 2) ≢
  shapedRewardCode negativeQMunchausenMode one8 (int8OfNat 2)
standardAndNegativeAreDistinctWitness neq = neq refl
