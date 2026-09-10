{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_DoubleSign_Composed_v152 where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.EfficientCHAD_CReLU_Tsallis2_v150
open import Exotic.ERL.FullCoupled.EfficientCHAD_DoubleSign_v151

record DoubleSignCompositionLaw (A : OrderedAlgebra) : Set₁ where
  field
    inner outer : SignActivationCertificate A
    absorb : ∀ x →
      SignActivationCertificate.sign outer
        (SignActivationCertificate.sign inner x) ≡
      SignActivationCertificate.sign inner x

composeSign : ∀ {A : OrderedAlgebra} {n : Nat}
  → DoubleSignCompositionLaw A → Vector A n → Vector A n
composeSign c [] = []
composeSign c (x ∷ xs) =
  SignActivationCertificate.sign
    (DoubleSignCompositionLaw.outer c)
    (SignActivationCertificate.sign
      (DoubleSignCompositionLaw.inner c) x)
  ∷ composeSign c xs

composeSignCorrect : ∀ {A : OrderedAlgebra} {n : Nat}
  (c : DoubleSignCompositionLaw A) (x : Vector A n) →
  composeSign c x ≡ signVec (DoubleSignCompositionLaw.inner c) x
composeSignCorrect c [] = refl
composeSignCorrect c (x ∷ xs) =
  cong₂ _∷_
    (DoubleSignCompositionLaw.absorb c x)
    (composeSignCorrect c xs)

sameSignCompositionLaw : ∀ {A : OrderedAlgebra}
  (s : SignActivationCertificate A) →
  DoubleSignCompositionLaw A
sameSignCompositionLaw s = record
  { inner = s
  ; outer = s
  ; absorb = SignActivationCertificate.signIdempotent s
  }

record FiniteKKTFixedPointLaw
  (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    relation : Vector A n → Vector A n → Set
    stationarity feasible complementarity : Vector A n → Set
    point : Vector A n
    fixed : relation point point
    stationary : stationarity point
    feasibleAt : feasible point
    complementaryAt : complementarity point

record DoubleSignComposedCertificate
  (A : OrderedAlgebra) (n window : Nat) : Set₁ where
  field
    stack : PredictivePrescriptiveConjectureCertificate A n window
    composition : DoubleSignCompositionLaw A
    interpolation : FiniteInterpolationCertificate A
    nonsmooth : FiniteKKTFixedPointLaw A n
    pareto : ParetoEfficientMappingCertificate A
    predictedNorm : OrderedAlgebra.R A

composeDoubleSignComposedCertificate : ∀
  {A : OrderedAlgebra} {n window : Nat} →
  DoubleSignComposedCertificate A n window →
  DoubleSignComposedCertificate A n window
composeDoubleSignComposedCertificate c = c
