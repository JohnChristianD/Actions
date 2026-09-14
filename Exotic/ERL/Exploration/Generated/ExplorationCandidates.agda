{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.Generated.ExplorationCandidates where

-- Generated flat-dyadic × method full-composition theorem harness.
-- Haskell constructs source; Agda --safe is the acceptance oracle.
open import Exotic.ERL.Exploration.DyadicLaw using
  ( DyadicLaw; flatDyadic; flatDyadicNormalized; flatDyadicUnitSupport )
open import Exotic.ERL.FullCoupled.FullAlgebraicCoupling using
  ( FullAlgebraicCoupling; composeFull )
open import Exotic.efficient_chad.SoftsignGatedComposition using
  ( softsignGatedForwardLaw-proof; softsignGatedPullbackLaw-proof )
open import Exotic.efficient_chad.MobiusSoftsignBridge using
  ( softsignGatedForwardMobiusWitness )
open import Exotic.ERL.FullCoupled.SoftsignGatedRepresentation using
  ( softsignGatedPeriodOne )
open import Exotic.ERL.FullCoupled.TheoremStrengthV3 using
  ( OpenES-lt-MR15; MR15-lt-NoisyNet; openES-lt-NoisyNet
  ; openESFullFromMR15Full; mr15FullFromNoisyNetFull )
open import Exotic.ERL.Exploration.FlatDyadicEligibility using
  ( flatDyadicAllFiniteEligibility )

FlatDyadicEligibility = flatDyadicAllFiniteEligibility

open import Exotic.ERL.Exploration.MR15Reachability

MR15FlatDyadicEndogenous : FullAlgebraicCoupling flatDyadic MR15Step
MR15FlatDyadicEndogenous = composeFull flatDyadic flatDyadicNormalized
  flatDyadicUnitSupport softsignGatedForwardLaw-proof
  softsignGatedPullbackLaw-proof softsignGatedForwardMobiusWitness
  softsignGatedPeriodOne mr15IrreducibilityProof mr15SelfLoopProof

open import Exotic.ERL.Exploration.OpenESDyadic

OpenESFlatDyadicEndogenous : FullAlgebraicCoupling flatDyadic openESStep
OpenESFlatDyadicEndogenous = composeFull flatDyadic flatDyadicNormalized
  flatDyadicUnitSupport softsignGatedForwardLaw-proof
  softsignGatedPullbackLaw-proof softsignGatedForwardMobiusWitness
  softsignGatedPeriodOne openESIrreducibilityProof openESSelfLoopProof

open import Exotic.ERL.FullCoupled.NoisyNetCoupled

NoisyNetFlatDyadicEndogenous : FullAlgebraicCoupling flatDyadic NoisyNetStep
NoisyNetFlatDyadicEndogenous = composeFull flatDyadic flatDyadicNormalized
  flatDyadicUnitSupport softsignGatedForwardLaw-proof
  softsignGatedPullbackLaw-proof softsignGatedForwardMobiusWitness
  softsignGatedPeriodOne noisyNetIrreducibilityProof noisyNetSelfLoopProof

StrictOpenESLTMR15 = OpenES-lt-MR15
StrictMR15LTNoisyNet = MR15-lt-NoisyNet
StrictOpenESLTNoisyNet = openES-lt-NoisyNet
FullOpenESLTMR15 = openESFullFromMR15Full
FullMR15LTNoisyNet = mr15FullFromNoisyNetFull
