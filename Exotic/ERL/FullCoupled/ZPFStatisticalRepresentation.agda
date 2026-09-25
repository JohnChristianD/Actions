{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Typed ZPF / omega^3 semantic boundary for the canonical GRU layer.
--
-- The physical ZPF carrier, Maxwell constraints, stochastic semantics,
-- and spectral convention are explicit inputs.  The module does not
-- manufacture a physical ZPF inhabitant.
--
-- The omega^3 law is represented by an explicit spectral-density carrier:
-- a concrete instantiation decides the frequency measure and normalization
-- (for example, per unit angular frequency).  This keeps the formal
-- statement honest about convention without introducing a new arithmetic
-- dependency into the repository.
--
-- Once a ZPF -> canonical-GRU statistical representation supplies
-- decode (encode z) == z, global injectivity follows from the existing
-- carrier-polymorphic statistical representation theorem.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.ZPFStatisticalRepresentation where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Exotic.ERL.FullCoupled.GRUStatisticalInjectivity as G
open import Exotic.ERL.FullCoupled.TsallisStatisticalRepresentation public

record ZPFOmegaCubedSpectralLaw
  (ZPFState Frequency SpectralDensity : Set)
  (frequencyMultiply : Frequency → Frequency → Frequency) : Set₁ where
  constructor zpfOmegaCubedSpectralLaw
  field
    density :
      ZPFState → Frequency → SpectralDensity
    spectralDensityOfOmegaCubed :
      Frequency → SpectralDensity
    omegaCubed :
      Frequency → Frequency
    omegaCubedDefinition :
      ∀ (ω : Frequency) →
      omegaCubed ω ≡
      frequencyMultiply (frequencyMultiply ω ω) ω
    omegaCubedLaw :
      ∀ (z : ZPFState) (ω : Frequency) →
      density z ω ≡ spectralDensityOfOmegaCubed (omegaCubed ω)

open ZPFOmegaCubedSpectralLaw public

record ZPFMaxwellSemanticData
  (ZPFState MaxwellField Frequency SpectralDensity : Set)
  (frequencyMultiply : Frequency → Frequency → Frequency)
  (Homogeneous Isotropic Maxwell : MaxwellField → Set)
  (Stochastic : ZPFState → Set) : Set₁ where
  constructor zpfMaxwellSemanticData
  field
    fieldZPF :
      ZPFState → MaxwellField
    homogeneous :
      ∀ z → Homogeneous (fieldZPF z)
    isotropic :
      ∀ z → Isotropic (fieldZPF z)
    stochastic :
      ∀ z → Stochastic z
    maxwell :
      ∀ z → Maxwell (fieldZPF z)
    spectralLaw :
      ZPFOmegaCubedSpectralLaw
        ZPFState
        Frequency
        SpectralDensity
        frequencyMultiply

open ZPFMaxwellSemanticData public

record ZPFGRUStatisticalRepresentation
  (ZPFState Frequency SpectralDensity MaxwellField : Set)
  (Homogeneous Isotropic Maxwell : MaxwellField → Set)
  (Stochastic : ZPFState → Set) : Set₁ where
  constructor zpfGRUStatisticalRepresentation
  field
    zpfSemantics :
      ZPFMaxwellSemanticData
        ZPFState
        MaxwellField
        Frequency
        SpectralDensity
        frequencyMultiply
        Homogeneous
        Isotropic
        Maxwell
        Stochastic
    statisticalRepresentation :
      CarrierPolymorphicStatisticalRepresentation
        ZPFState
        G.CanonicalGRUStatisticalObservation

open ZPFGRUStatisticalRepresentation public

zpfGRUStatisticalEncodeInjective :
  ∀ {ZPFState Frequency SpectralDensity MaxwellField : Set}
  {Homogeneous Isotropic Maxwell : MaxwellField → Set}
  {Stochastic : ZPFState → Set}
  (R :
    ZPFGRUStatisticalRepresentation
      ZPFState
      Frequency
      SpectralDensity
      MaxwellField
      Homogeneous
      Isotropic
      Maxwell
      Stochastic)
  {z₁ z₂ : ZPFState} →
  encode (statisticalRepresentation R) z₁ ≡
  encode (statisticalRepresentation R) z₂ →
  z₁ ≡ z₂
zpfGRUStatisticalEncodeInjective R =
  statisticalEncodeInjective (statisticalRepresentation R)

zpfGRUStatisticalDistinguishes :
  ∀ {ZPFState Frequency SpectralDensity MaxwellField : Set}
  {Homogeneous Isotropic Maxwell : MaxwellField → Set}
  {Stochastic : ZPFState → Set}
  (R :
    ZPFGRUStatisticalRepresentation
      ZPFState
      Frequency
      SpectralDensity
      MaxwellField
      Homogeneous
      Isotropic
      Maxwell
      Stochastic)
  {z₁ z₂ : ZPFState} →
  z₁ ≢ z₂ →
  encode (statisticalRepresentation R) z₁ ≢
  encode (statisticalRepresentation R) z₂
zpfGRUStatisticalDistinguishes R =
  statisticalEncodeDistinguishes (statisticalRepresentation R)

record ZPFGRUGlobalInjectivityTheorem
  (ZPFState Frequency SpectralDensity MaxwellField : Set)
  (Homogeneous Isotropic Maxwell : MaxwellField → Set)
  (Stochastic : ZPFState → Set) : Set₁ where
  constructor zpfGRUGlobalInjectivityTheoremWitness
  field
    representation :
      ZPFGRUStatisticalRepresentation
        ZPFState
        Frequency
        SpectralDensity
        MaxwellField
        Homogeneous
        Isotropic
        Maxwell
        Stochastic
    globalInjective :
      ∀ {z₁ z₂ : ZPFState} →
      encode (statisticalRepresentation representation) z₁ ≡
      encode (statisticalRepresentation representation) z₂ →
      z₁ ≡ z₂

zpfGRUGlobalInjectivityTheorem :
  ∀ {ZPFState Frequency SpectralDensity MaxwellField : Set}
  {Homogeneous Isotropic Maxwell : MaxwellField → Set}
  {Stochastic : ZPFState → Set} →
  ZPFGRUStatisticalRepresentation
    ZPFState
    Frequency
    SpectralDensity
    MaxwellField
    Homogeneous
    Isotropic
    Maxwell
    Stochastic →
  ZPFGRUGlobalInjectivityTheorem
    ZPFState
    Frequency
    SpectralDensity
    MaxwellField
    Homogeneous
    Isotropic
    Maxwell
    Stochastic
zpfGRUGlobalInjectivityTheorem R =
  zpfGRUGlobalInjectivityTheoremWitness
    R
    (zpfGRUStatisticalEncodeInjective R)
