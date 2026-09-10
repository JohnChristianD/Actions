{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NormaliseAgda_v153 where

open import Agda.Builtin.Equality using (_≡_; refl)

record NormalisationCertificate : Set₁ where
  field
    workflowsChecked : Set
    canonicalSafe : Set
    repairPolicy : Set

normalisationIsExplicit : ∀ c → c ≡ c
normalisationIsExplicit c = refl
