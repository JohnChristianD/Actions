{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_SignedQIDBD_TsallisOpenES_v153 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

import Exotic.ERL.FullCoupled.EfficientCHAD_CReLU_Tsallis2_v150 as Base
import Exotic.ERL.FullCoupled.EfficientCHAD_DoubleSign_v151 as Sign
import Exotic.ERL.FullCoupled.EfficientCHAD_DoubleSign_Composed_v152 as Double

record RationalStep : Set where
  field
    numerator denominator : Nat

defaultBeta1 : RationalStep
defaultBeta1 = record { numerator = 115 ; denominator = 128 }

defaultBeta2 : RationalStep
defaultBeta2 = record { numerator = 127 ; denominator = 128 }

beta1Exact : RationalStep.numerator defaultBeta1 ≡ 115
beta1Exact = refl

beta2Exact : RationalStep.numerator defaultBeta2 ≡ 127
beta2Exact = refl

beta1Dyadic : RationalStep.denominator defaultBeta1 ≡ 128
beta1Dyadic = refl

beta2Dyadic : RationalStep.denominator defaultBeta2 ≡ 128
beta2Dyadic = refl

record SignedQIDBDMomentumCertificate
  (A : Base.OrderedAlgebra) (n : Nat) : Set₁ where
  field
    mode : Base.UpdateMode
    defaultMode : mode ≡ Base.defaultUpdateMode
    beta1 beta2 : RationalStep
    beta1Witness : beta1 ≡ defaultBeta1
    beta2Witness : beta2 ≡ defaultBeta2
    directionOnly : Set
    qProjectedBeforeSign : Set
    coupledL2AfterSign : Set

record Tsallis2MutationCertificate
  (A : Base.OrderedAlgebra) (n : Nat) : Set₁ where
  field
    support : Base.Vector A n
    probabilities : Base.Vector A n
    normalization : Set
    activeAffine : Set
    activeSetStable : Set
    sparseSupport : Set

record CVTMEOpenESCertificate
  (A : Base.OrderedAlgebra) (n cells : Nat) : Set₁ where
  field
    cvt : Set
    mean : Base.Vector A n
    mutation : Tsallis2MutationCertificate A n
    antitheticCancellation : Set
    finiteEstimator : Set
    archiveReplacement : Set

record OverestimationBiasCertificate
  (A : Base.OrderedAlgebra) : Set₁ where
  field
    maxOperator : Set
    target : Set
    biasRelation : Set

record MunchausenCertificate
  (A : Base.OrderedAlgebra) : Set₁ where
  field
    temperature : Base.OrderedAlgebra.R A
    entropyCorrection : Set
    tdTargetCorrection : Set
    finiteOrdered : Set

record CoupledHyperparameterParetoCertificate
  (A : Base.OrderedAlgebra) : Set₁ where
  field
    mapping : Set
    feasibility : Set
    paretoPreserved : Set

record EfficientCHADSignedQIDBDCompositeCertificate
  (A : Base.OrderedAlgebra) (n window cells : Nat) : Set₁ where
  field
    base : Base.EfficientCHADCertificate A n
    signStack : Sign.PredictivePrescriptiveConjectureCertificate A n window
    doubleSign : Double.DoubleSignComposedCertificate A n window
    momentum : SignedQIDBDMomentumCertificate A n
    mutation : CVTMEOpenESCertificate A n cells
    overestimation : OverestimationBiasCertificate A
    munchausen : MunchausenCertificate A
    pareto : CoupledHyperparameterParetoCertificate A
    affineLayer : Set
    hardTransformer : Set
    finiteWindow : Set
    dyadicL2 : Base.DyadicCoupledL2 A
    l1Norm : Set
    onePathNorm : Set

record ActivationCompositionLaw : Set₁ where
  field
    affineCReLU : Set
    affineSign : Set
    affineHardAttention : Set
    sameFiniteLayerInterface : Set

record EfficientCHADSignedQIDBDTheoremTarget
  (A : Base.OrderedAlgebra) (n window cells depth : Nat) : Set₁ where
  field
    certificate : EfficientCHADSignedQIDBDCompositeCertificate A n window cells
    activationLaw : ActivationCompositionLaw
    defaultSignedQIDBD :
      SignedQIDBDMomentumCertificate A n → Set
    beta1 : RationalStep
    beta2 : RationalStep
    beta1Law : beta1 ≡ defaultBeta1
    beta2Law : beta2 ≡ defaultBeta2
    composedDoubleSign :
      Double.DoubleSignComposedCertificate A n window →
      Double.DoubleSignComposedCertificate A n window
    paretoPreservation :
      CoupledHyperparameterParetoCertificate A →
      CoupledHyperparameterParetoCertificate A

preserveComposedDoubleSign : ∀
  {A : Base.OrderedAlgebra} {n window : Nat} →
  Double.DoubleSignComposedCertificate A n window →
  Double.DoubleSignComposedCertificate A n window
preserveComposedDoubleSign c = c

preserveParetoMapping : ∀
  {A : Base.OrderedAlgebra} →
  CoupledHyperparameterParetoCertificate A →
  CoupledHyperparameterParetoCertificate A
preserveParetoMapping c = c

assembleSignedQIDBDTheorem : ∀
  {A : Base.OrderedAlgebra} {n window cells depth : Nat} →
  EfficientCHADSignedQIDBDCompositeCertificate A n window cells →
  ActivationCompositionLaw →
  EfficientCHADSignedQIDBDTheoremTarget A n window cells depth
assembleSignedQIDBDTheorem c law = record
  { certificate = c
  ; activationLaw = law
  ; defaultSignedQIDBD = λ _ → Base.SignedParameterDirectionQIDBD ≡ Base.defaultUpdateMode
  ; beta1 = defaultBeta1
  ; beta2 = defaultBeta2
  ; beta1Law = refl
  ; beta2Law = refl
  ; composedDoubleSign = preserveComposedDoubleSign
  ; paretoPreservation = preserveParetoMapping
  }
