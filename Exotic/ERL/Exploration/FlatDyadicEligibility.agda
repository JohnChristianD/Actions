{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.FlatDyadicEligibility where

open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne
  ; there
  ; here
  )
open import Exotic.ERL.Exploration.FlatDyadic using
  ( flatWeight
  ; flatDenominator
  ; flatWeight-sum
  ; flatStay-positive
  ; flatAny-positive
  )

data FlatKernel : Fin 256 → Fin 256 → Set where
  flatTarget : ∀ {s t} → flatWeight t ≡ 1 → FlatKernel s t

flatKernelIrreducible : Irreducible FlatKernel
flatKernelIrreducible s t = there (flatTarget (flatAny-positive t)) here

flatKernelSelfLoop : SelfLoop FlatKernel
flatKernelSelfLoop s = flatTarget (flatAny-positive s)

flatKernelPeriodOne : PeriodOne FlatKernel
flatKernelPeriodOne =
  periodOne flatKernelIrreducible flatKernelSelfLoop

flatDyadic : flatDenominator ≡ 256
flatDyadic = refl

flatScaleInvariant :
  ∀ (scale : Fin 256 → Fin 256) (x : Fin 256)
  → flatWeight (scale x) ≡ flatWeight x
flatScaleInvariant scale x = refl

flatSymmetric :
  ∀ (mirror : Fin 256 → Fin 256) (x : Fin 256)
  → flatWeight (mirror x) ≡ flatWeight x
flatSymmetric mirror x = refl

flatWeaklyUnimodal :
  ∀ (x y : Fin 256) → flatWeight x ≡ flatWeight y
flatWeaklyUnimodal x y = refl

flatAperiodic : SelfLoop FlatKernel
flatAperiodic = flatKernelSelfLoop

flatIrreducible : Irreducible FlatKernel
flatIrreducible = flatKernelIrreducible

record FlatDyadicEligibility : Set₁ where
  constructor flatDyadicEligibility
  field
    normalized : flatWeight-sum
    dyadicDenominator : flatDenominator ≡ 256
    scaleInvariant : ∀ (scale : Fin 256 → Fin 256) (x : Fin 256)
      → flatWeight (scale x) ≡ flatWeight x
    symmetric : ∀ (mirror : Fin 256 → Fin 256) (x : Fin 256)
      → flatWeight (mirror x) ≡ flatWeight x
    weaklyUnimodal : ∀ (x y : Fin 256) → flatWeight x ≡ flatWeight y
    aperiodic : SelfLoop FlatKernel
    irreducible : Irreducible FlatKernel

flatDyadicAllFiniteEligibility : FlatDyadicEligibility
flatDyadicAllFiniteEligibility =
  flatDyadicEligibility
    flatWeight-sum
    flatDyadic
    flatScaleInvariant
    flatSymmetric
    flatWeaklyUnimodal
    flatAperiodic
    flatIrreducible
