{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_DoubleSign_v151 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Exotic.ERL.FullCoupled.EfficientCHAD_CReLU_Tsallis2_v150

cong₂ :
  {A B C : Set} →
  (f : A → B → C) →
  {x x' : A} →
  {y y' : B} →
  x ≡ x' →
  y ≡ y' →
  f x y ≡ f x' y'
cong₂ f refl refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

record SignActivationCertificate (A : OrderedAlgebra) : Set₁ where
  field
    sign : OrderedAlgebra.R A → OrderedAlgebra.R A
    signIdempotent : ∀ x → sign (sign x) ≡ sign x
    signAbsPreserving : ∀ x →
      OrderedAlgebra.abs A (sign x) ≡ OrderedAlgebra.abs A x

open SignActivationCertificate

signVec : ∀ {A n} → SignActivationCertificate A → Vector A n → Vector A n
signVec s [] = []
signVec s (x ∷ xs) = sign s x ∷ signVec s xs

signMatrix : ∀ {A m n} → SignActivationCertificate A → Matrix A m n → Matrix A m n
signMatrix s [] = []
signMatrix s (r ∷ rs) = signVec s r ∷ signMatrix s rs

signVec₂ : ∀ {A n} → SignActivationCertificate A → Vector A n → Vector A n
signVec₂ s x = signVec s (signVec s x)

signMatrix₂ : ∀ {A m n} → SignActivationCertificate A → Matrix A m n → Matrix A m n
signMatrix₂ s W = signMatrix s (signMatrix s W)

signDoubleVec : ∀ {A n} (s : SignActivationCertificate A) (x : Vector A n) →
  signVec₂ s x ≡ signVec s x
signDoubleVec s [] = refl
signDoubleVec s (x ∷ xs) =
  cong₂ _∷_ (SignActivationCertificate.signIdempotent s x)
    (signDoubleVec s xs)

signDoubleMatrix : ∀ {A m n} (s : SignActivationCertificate A) (W : Matrix A m n) →
  signMatrix₂ s W ≡ signMatrix s W
signDoubleMatrix s [] = refl
signDoubleMatrix s (r ∷ rs) =
  cong₂ _∷_ (signDoubleVec s r) (signDoubleMatrix s rs)

rowL1Sign : ∀ {A n} (A₀ : OrderedAlgebra)
  (s : SignActivationCertificate A₀)
  (x : Vec (OrderedAlgebra.R A₀) n) →
  rowL1 A₀ (signVec s x) ≡ rowL1 A₀ x
rowL1Sign A₀ s [] = refl
rowL1Sign A₀ s (x ∷ xs) =
  cong₂ (OrderedAlgebra._+_ A₀)
    (SignActivationCertificate.signAbsPreserving s x)
    (rowL1Sign A₀ s xs)

weightL1Sign : ∀ {A m n} (A₀ : OrderedAlgebra)
  (s : SignActivationCertificate A₀)
  (W : Matrix A₀ m n) →
  weightL1 A₀ (signMatrix s W) ≡ weightL1 A₀ W
weightL1Sign A₀ s [] = refl
weightL1Sign A₀ s (r ∷ rs) =
  cong₂ (OrderedAlgebra._+_ A₀)
    (rowL1Sign A₀ s r)
    (weightL1Sign A₀ s rs)

pathRowSign : ∀ {A h i} (A₀ : OrderedAlgebra)
  (s : SignActivationCertificate A₀)
  (a : Vec (OrderedAlgebra.R A₀) h)
  (W : Matrix A₀ h i) →
  pathRow A₀ (signVec s a) (signMatrix s W) ≡
  pathRow A₀ a W
pathRowSign A₀ s [] [] = refl
pathRowSign A₀ s (a ∷ as) (r ∷ rs) =
  cong₂ (OrderedAlgebra._+_ A₀)
    (cong₂ (OrderedAlgebra._*_ A₀)
      (SignActivationCertificate.signAbsPreserving s a)
      (rowL1Sign A₀ s r))
    (pathRowSign A₀ s as rs)

onePathNormSign : ∀ {A h i o} (A₀ : OrderedAlgebra)
  (s : SignActivationCertificate A₀)
  (W₁ : Matrix A₀ h i) (W₂ : Matrix A₀ o h) →
  onePathNorm A₀ (signMatrix s W₁) (signMatrix s W₂) ≡
  onePathNorm A₀ W₁ W₂
onePathNormSign A₀ s W₁ [] = refl
onePathNormSign A₀ s W₁ (r ∷ rs) =
  cong₂ (OrderedAlgebra._+_ A₀)
    (pathRowSign A₀ s r W₁)
    (onePathNormSign A₀ s W₁ rs)

onePathNormDoubleSign : ∀ {A h i o} (A₀ : OrderedAlgebra)
  (s : SignActivationCertificate A₀)
  (W₁ : Matrix A₀ h i) (W₂ : Matrix A₀ o h) →
  onePathNorm A₀ (signMatrix₂ s W₁) (signMatrix₂ s W₂) ≡
  onePathNorm A₀ W₁ W₂
onePathNormDoubleSign A₀ s W₁ W₂ =
  trans
    (cong₂ (λ X Y → onePathNorm A₀ X Y)
      (signDoubleMatrix s W₁)
      (signDoubleMatrix s W₂))
    (onePathNormSign A₀ s W₁ W₂)

record FixedWindowHardAttentionCertificate
  (A : OrderedAlgebra) (window : Nat) : Set₁ where
  field
    score : Fin window → OrderedAlgebra.R A
    winner : Fin window
    winnerMax : ∀ j →
      OrderedAlgebra._≤_ A (score j) (score winner)

record FixedWindowHardTransformerCertificate
  (A : OrderedAlgebra) (window : Nat) : Set₁ where
  field
    context : Vec (OrderedAlgebra.R A) window
    query : OrderedAlgebra.R A
    score : Fin window → OrderedAlgebra.R A
    winner : Fin window
    winnerMax : ∀ j →
      OrderedAlgebra._≤_ A (score j) (score winner)
    nextContext : Vec (OrderedAlgebra.R A) window

record CoupledHyperParameterCertificate (A : OrderedAlgebra) : Set₁ where
  field
    traceProduct projectionBudget effectiveDecay metaStep smoothTau cemRate :
      OrderedAlgebra.R A

record CoupledParetoCoordinateCertificate (A : OrderedAlgebra) : Set₁ where
  field
    traceProduct projectionBudget effectiveDecay metaStep smoothTau cemRate :
      OrderedAlgebra.R A

record ParetoEfficientMappingCertificate (A : OrderedAlgebra) : Set₁ where
  field
    map : CoupledHyperParameterCertificate A → CoupledParetoCoordinateCertificate A
    efficient : CoupledHyperParameterCertificate A → Set
    efficiencyWitness : ∀ h → efficient h

record PredictivePrescriptiveConjectureCertificate
  (A : OrderedAlgebra) (n window : Nat) : Set₁ where
  field
    base : EfficientCHADCertificate A n
    sign : SignActivationCertificate A
    attention : FixedWindowHardAttentionCertificate A window
    transformer : FixedWindowHardTransformerCertificate A window
    pareto : ParetoEfficientMappingCertificate A
    predictedNorm : OrderedAlgebra.R A
    prescribedMode : UpdateMode
    conjecture : Set

record FiniteInterpolationCertificate (A : OrderedAlgebra) : Set₁ where
  field
    interpolate : OrderedAlgebra.R A →
      OrderedAlgebra.R A → OrderedAlgebra.R A → OrderedAlgebra.R A
    leftEndpoint : ∀ x y →
      interpolate x y (OrderedAlgebra.zero A) ≡ x
    rightEndpoint : ∀ x y →
      interpolate x y (OrderedAlgebra.one A) ≡ y

record EfficientCHAD_DoubleSign_TheoremTarget
  (A : OrderedAlgebra) (n window : Nat) : Set₁ where
  field
    stack : PredictivePrescriptiveConjectureCertificate A n window
    interpolation : FiniteInterpolationCertificate A
    doubleSignVec : ∀ x →
      signVec₂
        (PredictivePrescriptiveConjectureCertificate.sign stack) x ≡
      signVec
        (PredictivePrescriptiveConjectureCertificate.sign stack) x
    doubleSignMatrix : ∀ {m} (W : Matrix A m n) →
      signMatrix₂
        (PredictivePrescriptiveConjectureCertificate.sign stack) W ≡
      signMatrix
        (PredictivePrescriptiveConjectureCertificate.sign stack) W

composeDoubleSignTarget : ∀ {A n window}
  (stack : PredictivePrescriptiveConjectureCertificate A n window)
  (interpolation : FiniteInterpolationCertificate A) →
  EfficientCHAD_DoubleSign_TheoremTarget A n window
composeDoubleSignTarget stack interpolation = record
  { stack = stack
  ; interpolation = interpolation
  ; doubleSignVec = signDoubleVec
      (PredictivePrescriptiveConjectureCertificate.sign stack)
  ; doubleSignMatrix = λ W → signDoubleMatrix
      (PredictivePrescriptiveConjectureCertificate.sign stack) W
  }

record FiniteDifferentialInclusionCertificate
  (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    relation : Vector A n → Vector A n → Set
    selected : Vector A n → Vector A n → Set

record FiniteKKTCertificate
  (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    stationarity feasible complementarity : Vector A n → Set

record NonsmoothBridgeCertificate
  (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    differentialInclusion : FiniteDifferentialInclusionCertificate A n
    kkt : FiniteKKTCertificate A n
