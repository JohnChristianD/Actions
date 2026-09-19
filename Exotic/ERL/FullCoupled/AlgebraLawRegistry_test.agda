{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AlgebraLawRegistry_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc)
open import Data.List.Base using (List; []; _∷_)
open import Exotic.ERL.FullCoupled.AlgebraLawRegistry

registry-has-policy-composition :
  AlgebraLaw
registry-has-policy-composition = policyReplacementCompositionLaw

registry-has-ring-laws :
  AlgebraLaw
registry-has-ring-laws = ringDistributivityLaw

registry-composition-arity :
  AlgebraLawKind
registry-composition-arity = compositionLaw 2

registry-policy-composition :
  ∀ (K : C.FullLearnerKernel)
    (s : C.FullLearnerState)
    (rs : List C.LearnerReplacement) →
  C.canonicalPolicy K (C.applyLearnerReplacements rs s)
  ≡
  C.canonicalPolicy K s
registry-policy-composition =
  C.canonicalPolicy-learnerReplacement-composition

registry-compose-is-trans :
  ∀ {A : Set} {x y z : A} →
  x ≡ y →
  y ≡ z →
  x ≡ z
registry-compose-is-trans =
  λ first second →
    EqualityCompositionTheorem.composedStep
      (composeEqualityTheorem first second)
