{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ConjectureGeneration_v153 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.SignQIDBDComposed_v153

record PredictivePrescriptiveConjecture (A : OrderedAlgebra) : Set₁ where
  field
    system : CanonicalComposition A
    prediction : R A
    prescription : R A
    interpolation : DyadicInterpolation A
    statement : Set

record CertifiedPredictivePrescriptive (A : OrderedAlgebra) : Set₁ where
  field
    candidate : PredictivePrescriptiveConjecture A
    proof : PredictivePrescriptiveConjecture.statement candidate

promote : ∀ {A : OrderedAlgebra}
  (candidate : PredictivePrescriptiveConjecture A) →
  PredictivePrescriptiveConjecture.statement candidate →
  CertifiedPredictivePrescriptive A
promote candidate proof = record { candidate = candidate ; proof = proof }

candidateIdentity : ∀ {A : OrderedAlgebra}
  (c : PredictivePrescriptiveConjecture A) →
  PredictivePrescriptiveConjecture.prediction c ≡
  PredictivePrescriptiveConjecture.prediction c
candidateIdentity c = refl
