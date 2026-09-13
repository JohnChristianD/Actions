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
open import Exotic.ERL.FullCoupled.SoftsignGatedRepresentation using
  ( softsignGatedPeriodOne )
open import Exotic.ERL.FullCoupled.TheoremStrengthV3 using
  ( openES-lt-MR15; MR15-lt-NoisyNet; openES-lt-NoisyNet )

open import Exotic.ERL.Exploration.MR15Reachability

MR15FlatDyadicEndogenous : FullAlgebraicCoupling flatDyadic MR15Step
MR15FlatDyadicEndogenous = composeFull flatDyadic flatDyadicNormalized
  flatDyadicUnitSupport softsignGatedForwardLaw-proof
  softsignGatedPullbackLaw-proof softsignGatedPeriodOne
  mr15IrreducibilityProof mr15SelfLoopProof

open import Exotic.ERL.Exploration.OpenESDyadic

OpenESFlatDyadicEndogenous : FullAlgebraicCoupling flatDyadic openESStep
OpenESFlatDyadicEndogenous = composeFull flatDyadic flatDyadicNormalized
  flatDyadicUnitSupport softsignGatedForwardLaw-proof
  softsignGatedPullbackLaw-proof softsignGatedPeriodOne
  openESIrreducibilityProof openESSelfLoopProof

open import Exotic.ERL.FullCoupled.NoisyNetCoupled

NoisyNetFlatDyadicEndogenous : FullAlgebraicCoupling flatDyadic NoisyNetStep
NoisyNetFlatDyadicEndogenous = composeFull flatDyadic flatDyadicNormalized
  flatDyadicUnitSupport softsignGatedForwardLaw-proof
  softsignGatedPullbackLaw-proof softsignGatedPeriodOne
  noisyNetIrreducibilityProof noisyNetSelfLoopProof

StrictOpenESLTMR15 = openES-lt-MR15
StrictMR15LTNoisyNet = MR15-lt-NoisyNet
StrictOpenESLTNoisyNet = openES-lt-NoisyNet
