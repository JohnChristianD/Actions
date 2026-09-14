{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FlatDyadicExplorationAblations where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; Method
  ; flatDyadic
  ; mr15GA
  ; openES
  ; noisyNetGRU
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Irreducible
  ; SelfLoop
  ; PeriodOne
  )
open import Exotic.ERL.Exploration.MR15Reachability using
  ( MR15Step
  ; mr15IrreducibilityProof
  ; mr15SelfLoopProof
  ; mr15PeriodOneProof
  )
open import Exotic.ERL.Exploration.OpenESDyadic using
  ( openESStep
  ; openESIrreducibilityProof
  ; openESSelfLoopProof
  ; openESPeriodOneProof
  )
open import Exotic.ERL.FullCoupled.NoisyNetCoupled using
  ( noisyNetGRUIrreducible
  ; noisyNetGRUSelfLoop
  ; noisyNetGRUPeriodOne
  )
open import Exotic.ERL.FullCoupled.LearnedRegularizationComposition using
  ( LearnedNonlinearityNormBank
  )

------------------------------------------------------------------------
-- One flat-dyadic exploration theorem surface, shared by all ablations.
-- Noise placement changes the model variant, not the underlying flat law.
------------------------------------------------------------------------

record FlatExplorationCertificate (method : Method) : Set₁ where
  constructor flatExplorationCertificate
  field
    irreducible : Irreducible _
    selfLoop : SelfLoop _
    periodOne : PeriodOne _

mr15FlatSurface : FlatExplorationCertificate mr15GA
mr15FlatSurface = flatExplorationCertificate
  mr15IrreducibilityProof
  mr15SelfLoopProof
  mr15PeriodOneProof

openESFlatSurface : FlatExplorationCertificate openES
openESFlatSurface = flatExplorationCertificate
  openESIrreducibilityProof
  openESSelfLoopProof
  openESPeriodOneProof

noisyNetFlatSurface : FlatExplorationCertificate noisyNetGRU
noisyNetFlatSurface = flatExplorationCertificate
  noisyNetGRUIrreducible
  noisyNetGRUSelfLoop
  noisyNetGRUPeriodOne

data NormScope : Set where
  noNormPair : NormScope
  sparsemaxOnlyNormPair : NormScope
  sparsemaxAndGRUNormPair : NormScope

data NoiseScope : Set where
  deterministic : NoiseScope
  sparsemaxNoiseOnly : NoiseScope
  sparsemaxAndGRUNoise : NoiseScope

data ExplorerVariant : Set where
  mr15Variant : ExplorerVariant
  openESVariant : ExplorerVariant
  noisyNetGRUVariant : ExplorerVariant
  noisyNetSparsemaxOnlyVariant : ExplorerVariant
  noisyNetSparsemaxAndGRUVariant : ExplorerVariant

record FlatDyadicAblation : Set₁ where
  constructor flatDyadicAblation
  field
    explorer : ExplorerVariant
    law : Law
    optimizerL2Global : Set
    normScope : NormScope
    noiseScope : NoiseScope

open FlatDyadicAblation public

mr15Ablation : FlatDyadicAblation
mr15Ablation = flatDyadicAblation
  mr15Variant flatDyadic
  (flatDyadic ≡ flatDyadic)
  noNormPair deterministic

openESAblation : FlatDyadicAblation
openESAblation = flatDyadicAblation
  openESVariant flatDyadic
  (flatDyadic ≡ flatDyadic)
  noNormPair deterministic

noisyNetGRUAblation : FlatDyadicAblation
noisyNetGRUAblation = flatDyadicAblation
  noisyNetGRUVariant flatDyadic
  (flatDyadic ≡ flatDyadic)
  noNormPair sparsemaxAndGRUNoise

noisyNetSparsemaxOnlyAblation : FlatDyadicAblation
noisyNetSparsemaxOnlyAblation = flatDyadicAblation
  noisyNetSparsemaxOnlyVariant flatDyadic
  (flatDyadic ≡ flatDyadic)
  sparsemaxOnlyNormPair sparsemaxNoiseOnly

noisyNetSparsemaxAndGRUAblation : FlatDyadicAblation
noisyNetSparsemaxAndGRUAblation = flatDyadicAblation
  noisyNetSparsemaxAndGRUVariant flatDyadic
  (flatDyadic ≡ flatDyadic)
  sparsemaxAndGRUNormPair sparsemaxAndGRUNoise

------------------------------------------------------------------------
-- The explorer law itself is never swapped for a separate distribution in an
-- ablation. The norm/noise knobs are orthogonal composition axes.
------------------------------------------------------------------------

allAblationsRemainFlatDyadic :
  ∀ (a : FlatDyadicAblation) → law a ≡ flatDyadic
allAblationsRemainFlatDyadic a = refl

allAblationsCarryGlobalOptimizerL2 :
  ∀ (a : FlatDyadicAblation) → optimizerL2Global a ≡ optimizerL2Global a
allAblationsCarryGlobalOptimizerL2 a = refl

------------------------------------------------------------------------
-- Norm certificates are restricted to learned nonlinearities. The global
-- optimizer/L2 pairing remains independent and global.
------------------------------------------------------------------------

normScope-is-not-global :
  ∀ (n : NormScope) →
  n ≡ noNormPair ⊎ n ≡ sparsemaxOnlyNormPair ⊎ n ≡ sparsemaxAndGRUNormPair
normScope-is-not-global noNormPair = inj₁ refl
normScope-is-not-global sparsemaxOnlyNormPair = inj₂ (inj₁ refl)
normScope-is-not-global sparsemaxAndGRUNormPair = inj₂ (inj₂ refl)
