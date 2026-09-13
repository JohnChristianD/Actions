{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.Generated.ExplorationCandidates where

-- Generated method × probability-law full-composition proof harness.
-- Haskell constructs this source; Agda --safe is the acceptance oracle.
open import Exotic.ERL.Exploration.DyadicLaw using
  ( DyadicLaw
  ; lazyWalk
  ; dyadicLadder
  ; flatDyadic
  ; law-unit-support
  )
open import Exotic.ERL.FullCoupled.FullAlgebraicCoupling using
  ( FullAlgebraicCoupling
  ; composeFull
  )
open import Exotic.efficient_chad.SoftsignGatedComposition using
  ( softsignGatedForwardLaw-proof
  ; softsignGatedPullbackLaw-proof
  )

open import Exotic.ERL.Exploration.MR15Reachability

MR15LazyWalkEndogenous : FullAlgebraicCoupling lazyWalk MR15Step
MR15LazyWalkEndogenous = composeFull lazyWalk lazyWalkNormalized
  (law-unit-support lazyWalk)
  softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof
  mr15IrreducibilityProof mr15SelfLoopProof

MR15DyadicLadderEndogenous : FullAlgebraicCoupling dyadicLadder MR15Step
MR15DyadicLadderEndogenous = composeFull dyadicLadder dyadicLadderNormalized
  (law-unit-support dyadicLadder)
  softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof
  mr15IrreducibilityProof mr15SelfLoopProof

MR15FlatDyadicEndogenous : FullAlgebraicCoupling flatDyadic MR15Step
MR15FlatDyadicEndogenous = composeFull flatDyadic flatDyadicNormalized
  (law-unit-support flatDyadic)
  softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof
  mr15IrreducibilityProof mr15SelfLoopProof

open import Exotic.ERL.Exploration.OpenESDyadic

OpenESLazyWalkEndogenous : FullAlgebraicCoupling lazyWalk openESStep
OpenESLazyWalkEndogenous = composeFull lazyWalk lazyWalkNormalized
  (law-unit-support lazyWalk)
  softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof
  openESIrreducibilityProof openESSelfLoopProof

OpenESDyadicLadderEndogenous : FullAlgebraicCoupling dyadicLadder openESStep
OpenESDyadicLadderEndogenous = composeFull dyadicLadder dyadicLadderNormalized
  (law-unit-support dyadicLadder)
  softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof
  openESIrreducibilityProof openESSelfLoopProof

OpenESFlatDyadicEndogenous : FullAlgebraicCoupling flatDyadic openESStep
OpenESFlatDyadicEndogenous = composeFull flatDyadic flatDyadicNormalized
  (law-unit-support flatDyadic)
  softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof
  openESIrreducibilityProof openESSelfLoopProof

open import Exotic.ERL.FullCoupled.NoisyNetCoupled

NoisyNetLazyWalkEndogenous : FullAlgebraicCoupling lazyWalk NoisyNetStep
NoisyNetLazyWalkEndogenous = composeFull lazyWalk lazyWalkNormalized
  (law-unit-support lazyWalk)
  softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof
  noisyNetIrreducibilityProof noisyNetSelfLoopProof

NoisyNetDyadicLadderEndogenous : FullAlgebraicCoupling dyadicLadder NoisyNetStep
NoisyNetDyadicLadderEndogenous = composeFull dyadicLadder dyadicLadderNormalized
  (law-unit-support dyadicLadder)
  softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof
  noisyNetIrreducibilityProof noisyNetSelfLoopProof

NoisyNetFlatDyadicEndogenous : FullAlgebraicCoupling flatDyadic NoisyNetStep
NoisyNetFlatDyadicEndogenous = composeFull flatDyadic flatDyadicNormalized
  (law-unit-support flatDyadic)
  softsignGatedForwardLaw-proof softsignGatedPullbackLaw-proof
  noisyNetIrreducibilityProof noisyNetSelfLoopProof
