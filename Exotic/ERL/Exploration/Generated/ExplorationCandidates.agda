{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.Generated.ExplorationCandidates where

-- Generated law × method proof harness. Haskell only constructs this source; Agda --safe accepts it or rejects it.
open import Exotic.ERL.Exploration.DyadicLaw using
  ( DyadicLaw
  ; lazyWalk
  ; dyadicLadder
  )
open import Exotic.ERL.FullCoupled.FullAlgebraicCoupling using
  ( FullAlgebraicCoupling
  ; composeFull
  )

open import Exotic.ERL.Exploration.MR15Reachability

MR15LazyWalkEndogenous : FullAlgebraicCoupling lazyWalk MR15Step
MR15LazyWalkEndogenous = composeFull lazyWalk lazyWalkNormalized
  mr15IrreducibilityProof mr15SelfLoopProof

MR15DyadicLadderEndogenous : FullAlgebraicCoupling dyadicLadder MR15Step
MR15DyadicLadderEndogenous = composeFull dyadicLadder dyadicLadderNormalized
  mr15IrreducibilityProof mr15SelfLoopProof

open import Exotic.ERL.Exploration.OpenESDyadic

OpenESLazyWalkEndogenous : FullAlgebraicCoupling lazyWalk openESStep
OpenESLazyWalkEndogenous = composeFull lazyWalk lazyWalkNormalized
  openESIrreducibilityProof openESSelfLoopProof

OpenESDyadicLadderEndogenous : FullAlgebraicCoupling dyadicLadder openESStep
OpenESDyadicLadderEndogenous = composeFull dyadicLadder dyadicLadderNormalized
  openESIrreducibilityProof openESSelfLoopProof

open import Exotic.ERL.FullCoupled.NoisyNetCoupled

NoisyNetLazyWalkEndogenous : FullAlgebraicCoupling lazyWalk NoisyNetStep
NoisyNetLazyWalkEndogenous = composeFull lazyWalk lazyWalkNormalized
  noisyNetIrreducibilityProof noisyNetSelfLoopProof

NoisyNetDyadicLadderEndogenous : FullAlgebraicCoupling dyadicLadder NoisyNetStep
NoisyNetDyadicLadderEndogenous = composeFull dyadicLadder dyadicLadderNormalized
  noisyNetIrreducibilityProof noisyNetSelfLoopProof
