{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_DoubleSign_Composed_v152 where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
import Exotic.ERL.FullCoupled.EfficientCHAD_CReLU_Tsallis2_v150 as Base
import Exotic.ERL.FullCoupled.EfficientCHAD_DoubleSign_v151 as D
open Base

cong₂ :
  {A B C : Set} →
  (f : A → B → C) →
  {x x' : A} →
  {y y' : B} →
  x ≡ x' →
  y ≡ y' →
  f x y ≡ f x' y'
cong₂ f refl refl = refl

record DoubleSignCompositionLaw
  (A : Base.OrderedAlgebra) : Set₁ where
  field
    inner outer : D.SignActivationCertificate A
    absorb : ∀ x →
      D.SignActivationCertificate.sign outer
        (D.SignActivationCertificate.sign inner x) ≡
      D.SignActivationCertificate.sign inner x

composeSign : ∀ {A : Base.OrderedAlgebra} {n : Nat}
  → DoubleSignCompositionLaw A
  → Base.Vector A n
  → Base.Vector A n
composeSign c [] = []
composeSign c (x ∷ xs) =
  D.SignActivationCertificate.sign
    (DoubleSignCompositionLaw.outer c)
    (D.SignActivationCertificate.sign
      (DoubleSignCompositionLaw.inner c) x)
  ∷ composeSign c xs

composeSignCorrect : ∀ {A : Base.OrderedAlgebra} {n : Nat}
  (c : DoubleSignCompositionLaw A) (x : Base.Vector A n) →
  composeSign c x ≡
  D.signVec (DoubleSignCompositionLaw.inner c) x
composeSignCorrect c [] = refl
composeSignCorrect c (x ∷ xs) =
  cong₂ _∷_
    (DoubleSignCompositionLaw.absorb c x)
    (composeSignCorrect c xs)

sameSignCompositionLaw : ∀ {A : Base.OrderedAlgebra}
  (s : D.SignActivationCertificate A) →
  DoubleSignCompositionLaw A
sameSignCompositionLaw s = record
  { inner = s
  ; outer = s
  ; absorb = D.SignActivationCertificate.signIdempotent s
  }

sameSignCompositionLawCorrect : ∀ {A : Base.OrderedAlgebra} {n : Nat}
  (s : D.SignActivationCertificate A) (x : Base.Vector A n) →
  composeSign (sameSignCompositionLaw s) x ≡ D.signVec s x
sameSignCompositionLawCorrect s x = composeSignCorrect (sameSignCompositionLaw s) x

record FiniteKKTFixedPointLaw
  (A : Base.OrderedAlgebra) (n : Nat) : Set₁ where
  field
    relation : Base.Vector A n → Base.Vector A n → Set
    stationarity feasible complementarity : Base.Vector A n → Set
    point : Base.Vector A n
    fixed : relation point point
    stationary : stationarity point
    feasibleAt : feasible point
    complementaryAt : complementarity point

record DoubleSignComposedCertificate
  (A : Base.OrderedAlgebra) (n window : Nat) : Set₁ where
  field
    stack : D.PredictivePrescriptiveConjectureCertificate A n window
    composition : DoubleSignCompositionLaw A
    interpolation : D.FiniteInterpolationCertificate A
    nonsmooth : FiniteKKTFixedPointLaw A n
    pareto : D.ParetoEfficientMappingCertificate A
    predictedNorm : Base.OrderedAlgebra.R A

composeDoubleSignComposedCertificate : ∀
  {A : Base.OrderedAlgebra} {n window : Nat} →
  DoubleSignComposedCertificate A n window →
  DoubleSignComposedCertificate A n window
composeDoubleSignComposedCertificate c = c
