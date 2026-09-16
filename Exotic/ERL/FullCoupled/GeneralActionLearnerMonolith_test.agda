{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GeneralActionLearnerMonolith_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Fin using (Fin; fromℕ<)
open import Data.Nat.DivMod using (m%n<n)

open import Exotic.ERL.FullCoupled.GeneralActionLearnerMonolith

threeState : GeneralState 3
threeState = generalState zero zeroQ zeroCounts zeroGRU (fromℕ< (m%n<n 0 3))

fourState : GeneralState 4
fourState = generalState zero zeroQ zeroCounts zeroGRU (fromℕ< (m%n<n 0 4))

sixtyFourState : GeneralState 64
sixtyFourState = generalState zero zeroQ zeroCounts zeroGRU (fromℕ< (m%n<n 0 64))

threePolicy : Fin 3
threePolicy = generalPolicy (generalKernel noMunchausen) threeState

fourPolicy : Fin 4
fourPolicy = generalPolicy (generalKernel useMunchausen) fourState

sixtyFourPolicy : Fin 64
sixtyFourPolicy = generalPolicy (generalKernel noMunchausen) sixtyFourState

threeStepClock : clock (generalStep (generalKernel noMunchausen) threeState zero8) ≡ 1
threeStepClock = refl

sixtyFourStepClock : clock (generalStep (generalKernel useMunchausen) sixtyFourState one8) ≡ 1
sixtyFourStepClock = refl

threeSparseSupport :
  oneHotWeightA threePolicy threePolicy ≡ int8OfNat 128
threeSparseSupport = extremeSparsemaxSupportOne (λ a → scoreA (q threeState) (counts threeState) a)

fourSparseSupport :
  oneHotWeightA fourPolicy fourPolicy ≡ int8OfNat 128
fourSparseSupport = extremeSparsemaxSupportOne (λ a → scoreA (q fourState) (counts fourState) a)

genericCompositionLaw : ∀ (f g h : GeneralState 4 → GeneralState 4) s →
  composeStepAction (composeStepAction f g) h s ≡
  composeStepAction f (composeStepAction g h) s
genericCompositionLaw = composeStepAssociative
