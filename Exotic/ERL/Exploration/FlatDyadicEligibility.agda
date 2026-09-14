{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.FlatDyadicEligibility where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne
  ; there
  ; here
  )
open import Exotic.ERL.Exploration.DyadicLaws using
  ( flat-weight
  ; flat-normalized
  ; flat-scale-invariant
  ; flat-symmetric
  ; flat-weakly-unimodal
  ; flat-relabel-invariant
  ; FlatSupport
  ; flat-support
  )

-- The support predicate is lifted to the binary transition relation in
-- which every supported target is reachable in one step from every source.
flatKernel : Int8 → Int8 → Set
flatKernel _ t = FlatSupport t

flatKernelIrreducible : Irreducible flatKernel
flatKernelIrreducible s t = there (flat-support t) here

flatKernelSelfLoop : SelfLoop flatKernel
flatKernelSelfLoop s = flat-support s

flatKernelPeriodOne : PeriodOne flatKernel
flatKernelPeriodOne = periodOne flatKernelIrreducible flatKernelSelfLoop

flatDyadicDenominator : 256 ≡ 256
flatDyadicDenominator = refl

flatScaleInvariant :
  ∀ (scale : Int8 → Int8) (x : Int8) → flat-weight (scale x) ≡ flat-weight x
flatScaleInvariant = flat-scale-invariant

flatSymmetric :
  ∀ (mirror : Int8 → Int8) (x : Int8) → flat-weight (mirror x) ≡ flat-weight x
flatSymmetric = flat-symmetric

flatWeaklyUnimodal :
  ∀ (x y : Int8) → flat-weight x ≡ flat-weight y
flatWeaklyUnimodal = flat-weakly-unimodal

flatAllRelabelInvariant :
  ∀ (f : Int8 → Int8) (x : Int8) → flat-weight (f x) ≡ flat-weight x
flatAllRelabelInvariant = flat-relabel-invariant

record FlatDyadicEligibility : Set₁ where
  constructor flatDyadicEligibility
  field
    normalized : flat-normalized
    dyadicDenominator : flatDyadicDenominator
    scaleInvariant : ∀ (scale : Int8 → Int8) (x : Int8) → flat-weight (scale x) ≡ flat-weight x
    symmetric : ∀ (mirror : Int8 → Int8) (x : Int8) → flat-weight (mirror x) ≡ flat-weight x
    weaklyUnimodal : ∀ (x y : Int8) → flat-weight x ≡ flat-weight y
    allRelabelInvariant : ∀ (f : Int8 → Int8) (x : Int8) → flat-weight (f x) ≡ flat-weight x
    aperiodic : SelfLoop flatKernel
    irreducible : Irreducible flatKernel

flatDyadicAllFiniteEligibility : FlatDyadicEligibility
flatDyadicAllFiniteEligibility =
  flatDyadicEligibility
    flat-normalized
    flatDyadicDenominator
    flat-scale-invariant
    flat-symmetric
    flat-weakly-unimodal
    flat-relabel-invariant
    flatKernelSelfLoop
    flatKernelIrreducible
