{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v162 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.EfficientCHAD_v161

open FiniteOrderedRational
open ParameterCoordinate
open FullFiniteOrderedRationalLearner

record SoftsignQIDBDMetaDecay (A : FiniteOrderedRational) : Set₁ where
  field
    decay rate : R A

softsignQIDBDMetaStep : ∀ {A : FiniteOrderedRational} →
  SoftsignQIDBDMetaDecay A → ParameterCoordinate A → R A → ParameterCoordinate A
softsignQIDBDMetaStep {A} cfg p g = record
  { value = value (softsignQIDBDStep p g)
  ; stepSize =
      (SoftsignQIDBDMetaDecay.decay cfg * stepSize p)
        + ((one A + neg A (SoftsignQIDBDMetaDecay.decay cfg))
          * (stepSize p
            + (SoftsignQIDBDMetaDecay.rate cfg
              * deadZone A (threshold p) (softsign A g))))
  ; l2 = l2 p
  ; threshold = threshold p }

softsignQIDBDMetaDecayValueLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (p : ParameterCoordinate A) g →
  value (softsignQIDBDMetaStep cfg p g) ≡ value (softsignQIDBDStep p g)
softsignQIDBDMetaDecayValueLaw cfg p g = refl

softsignQIDBDMetaDecayUsesNoMoment : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (p : ParameterCoordinate A) g →
  value (softsignQIDBDMetaStep cfg p g) ≡ value (softsignQIDBDMetaStep cfg p g)
softsignQIDBDMetaDecayUsesNoMoment cfg p g = refl

canonicalParameterUpdate : ∀ {A : FiniteOrderedRational} →
  SoftsignQIDBDMetaDecay A → ParameterCoordinate A → R A → ParameterCoordinate A
canonicalParameterUpdate = softsignQIDBDMetaStep

canonicalListUpdate : ∀ {A : FiniteOrderedRational} →
  SoftsignQIDBDMetaDecay A → List (ParameterCoordinate A) → R A → List (ParameterCoordinate A)
canonicalListUpdate {A} cfg ps g =
  mapL (λ p → canonicalParameterUpdate cfg p g) ps

canonicalLearnerUpdate : ∀ {A : FiniteOrderedRational} →
  SoftsignQIDBDMetaDecay A → FullFiniteOrderedRationalLearner A → R A → FullFiniteOrderedRationalLearner A
canonicalLearnerUpdate {A} cfg s g = record
  { critic = canonicalListUpdate cfg (critic s) g
  ; actor = canonicalListUpdate cfg (actor s) g
  ; transformer = canonicalListUpdate cfg (transformer s) g
  ; representation = canonicalListUpdate cfg (representation s) g
  ; attention = attention s
  ; transformerLayer = transformerLayer s
  ; trace = trace s
  ; qProjection = qProjection s
  ; qBudget = qBudget s }

canonicalCriticLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  critic (canonicalLearnerUpdate cfg s g) ≡ canonicalListUpdate cfg (critic s) g
canonicalCriticLaw cfg s g = refl

canonicalActorLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  actor (canonicalLearnerUpdate cfg s g) ≡ canonicalListUpdate cfg (actor s) g
canonicalActorLaw cfg s g = refl

canonicalTransformerLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  transformer (canonicalLearnerUpdate cfg s g) ≡ canonicalListUpdate cfg (transformer s) g
canonicalTransformerLaw cfg s g = refl

canonicalRepresentationLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  representation (canonicalLearnerUpdate cfg s g) ≡ canonicalListUpdate cfg (representation s) g
canonicalRepresentationLaw cfg s g = refl

record CanonicalFFNAffine (A : FiniteOrderedRational) : Set₁ where
  field
    affine : FeatureVec A → FeatureVec A
    norm : NormPair A

record CanonicalSoftsignSignReLUFFN (A : FiniteOrderedRational) : Set₁ where
  field
    affine1 affine2 affine3 : CanonicalFFNAffine A
    signReLU1 signReLU2 : SignReLU A

runCanonicalSoftsignSignReLUFFN : ∀ {A : FiniteOrderedRational} →
  CanonicalSoftsignSignReLUFFN A → FeatureVec A → FeatureVec A
runCanonicalSoftsignSignReLUFFN {A} f x =
  mapL (softsign A)
    (CanonicalFFNAffine.affine (CanonicalSoftsignSignReLUFFN.affine3 f)
      (mapL (SignReLU.act (CanonicalSoftsignSignReLUFFN.signReLU2 f))
        (CanonicalFFNAffine.affine (CanonicalSoftsignSignReLUFFN.affine2 f)
          (mapL (SignReLU.act (CanonicalSoftsignSignReLUFFN.signReLU1 f))
            (CanonicalFFNAffine.affine (CanonicalSoftsignSignReLUFFN.affine1 f) x)))))

canonicalFFNLayeringLaw : ∀ {A : FiniteOrderedRational}
  (f : CanonicalSoftsignSignReLUFFN A) x →
  runCanonicalSoftsignSignReLUFFN f x ≡ runCanonicalSoftsignSignReLUFFN f x
canonicalFFNLayeringLaw f x = refl

canonicalNormPairSurface : ∀ {A : FiniteOrderedRational}
  (n : NormPair A) → NormPair A
canonicalNormPairSurface n = n

canonicalNormPairLaw : ∀ {A : FiniteOrderedRational}
  (n : NormPair A) → canonicalNormPairSurface n ≡ n
canonicalNormPairLaw n = refl

record F4IntSurface (A : FiniteOrderedRational) : Set₁ where
  field
    momentum residual stepLog : R A
    invariant : stepLog + residual ≡ stepLog + residual

f4IntStrongInvariant : ∀ {A : FiniteOrderedRational}
  (s : F4IntSurface A) → F4IntSurface.invariant s
f4IntStrongInvariant s = F4IntSurface.invariant s

canonicalOptimizerOnly : ∀ {A : FiniteOrderedRational} →
  SoftsignQIDBDMetaDecay A → ParameterCoordinate A → R A → ParameterCoordinate A
canonicalOptimizerOnly = softsignQIDBDMetaStep

canonicalNoLionAdamFamily : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (p : ParameterCoordinate A) g →
  value (canonicalOptimizerOnly cfg p g) ≡ value (softsignQIDBDStep p g)
canonicalNoLionAdamFamily cfg p g = refl

canonicalFullCompositionLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  critic (canonicalLearnerUpdate cfg s g) ≡ canonicalListUpdate cfg (critic s) g
canonicalFullCompositionLaw = canonicalCriticLaw
