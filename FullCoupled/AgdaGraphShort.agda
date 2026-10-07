{-# OPTIONS --guarded #-}

module FullCoupled.AgdaGraphShort where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Haskell.Prelude

import FullCoupled.CanonicalLearnerMonolith as C
import FullCoupled.TheoremsMonolith as T

record Surface (ℓ : Level) : Set (lsuc ℓ) where
  field
    State : Set ℓ
    step : State → State

CanonicalSurface : Surface (lsuc lzero)
CanonicalSurface = record
  { State = C.CanonicalFullLearnerState
  ; step = C.canonicalFullStep
  }

LearnerState : Set₁
LearnerState = C.CanonicalFullLearnerState

LearnerKernel : Set₁
LearnerKernel = C.CanonicalFullLearnerKernel

step : LearnerKernel → LearnerState → LearnerState
step = C.canonicalFullStep

policy : LearnerKernel → LearnerState → Nat
policy = C.canonicalPolicy
affine : C.MonoidAffine → C.Int8 → C.Int8
affine = C.applyMonoidAffine

lstm : List C.Int8 → C.Int8 → C.Int8
lstm = C.runMonoidLSTMCell

planAssoc :
  ∀ {Expression : Set} (xs ys zs : List Expression) →
  (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
planAssoc = T.aStar-plan-append-associative

policySelf :
  ∀ (K : LearnerKernel) (s : LearnerState) →
  policy K s ≡ policy K s
policySelf _ _ = refl
