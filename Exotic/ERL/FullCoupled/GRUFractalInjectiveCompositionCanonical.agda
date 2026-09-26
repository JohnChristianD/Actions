{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Canonical GRU instantiation of the fractal injective-composition kernel.
--
-- Nat indexes scale. The relation m ≤ n records refinement from a lower
-- level to an upper level. The canonical statistical observation is reused
-- unchanged at every scale, and the inter-level transport is the identity.
-- This is therefore an explicit scale-invariant self-similar instance,
-- not an assertion that every possible fractal representation is GRU
-- injective.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.GRUFractalInjectiveCompositionCanonical where

open import Agda.Builtin.Nat using (Nat; zero; suc; _≤_; z≤n)
open import Relation.Binary.PropositionalEquality using (refl)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.GRUStatisticalInjectivity
  using
  ( CanonicalGRUStatisticalObservation
  ; canonicalGRUStatisticalEncode
  ; canonicalGRUStatisticalDecode
  ; canonicalGRUStatisticalDecodeEncode
  )
open import Exotic.ERL.FullCoupled.GRUFractalInjectiveComposition

GRUFractalLevel : Set
GRUFractalLevel = Nat

GRUFractalRefines : GRUFractalLevel → GRUFractalLevel → Set
GRUFractalRefines lower upper = lower ≤ upper

canonicalGRUFractal : FractalInjectiveComposition
  GRUFractalLevel
  C.GRUState
  CanonicalGRUStatisticalObservation
  GRUFractalRefines
canonicalGRUFractal =
  fractalInjectiveComposition
    (λ _ → canonicalGRUStatisticalEncode)
    (λ _ → canonicalGRUStatisticalDecode)
    (λ level state → canonicalGRUStatisticalDecodeEncode state)
    (λ _ observation → observation)
    (λ eq → eq)
    (λ _ state → refl)

canonicalGRUFractalLevelInjective :
  ∀ level {s t : C.GRUState} →
  encode canonicalGRUFractal level s ≡
  encode canonicalGRUFractal level t →
  s ≡ t
canonicalGRUFractalLevelInjective =
  fractalLevelInjective canonicalGRUFractal

canonicalGRUFractalTransportedInjective :
  ∀ {lower upper : GRUFractalLevel}
  (r : GRUFractalRefines lower upper)
  {s t : C.GRUState} →
  transport canonicalGRUFractal r
    (encode canonicalGRUFractal lower s) ≡
  transport canonicalGRUFractal r
    (encode canonicalGRUFractal lower t) →
  s ≡ t
canonicalGRUFractalTransportedInjective =
  fractalTransportedEncodeInjective canonicalGRUFractal

canonicalGRUTwoScaleRefinement :
  GRUFractalRefines zero (suc zero)
canonicalGRUTwoScaleRefinement = z≤n

canonicalGRUTwoScaleInjective :
  ∀ {s t : C.GRUState} →
  transport canonicalGRUFractal canonicalGRUTwoScaleRefinement
    (encode canonicalGRUFractal zero s) ≡
  transport canonicalGRUFractal canonicalGRUTwoScaleRefinement
    (encode canonicalGRUFractal zero t) →
  s ≡ t
canonicalGRUTwoScaleInjective =
  canonicalGRUFractalTransportedInjective canonicalGRUTwoScaleRefinement
