{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.Generated.ExplorationCandidates where

-- Generated proof harness. Haskell only constructs this source; Agda --safe accepts it or rejects it.
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne-from-components
  )

open import Exotic.ERL.Exploration.MR15Reachability

MR15KernelIrreducibility : Irreducible MR15Step
MR15KernelIrreducibility = mr15IrreducibilityProof

MR15KernelSelfLoop : SelfLoop MR15Step
MR15KernelSelfLoop = mr15SelfLoopProof

MR15KernelPeriodOne : PeriodOne MR15Step
MR15KernelPeriodOne = periodOne-from-components MR15KernelIrreducibility MR15KernelSelfLoop

open import Exotic.ERL.Exploration.OpenESDyadic

OpenESKernelIrreducibility : Irreducible openESStep
OpenESKernelIrreducibility = openESIrreducibilityProof

OpenESKernelSelfLoop : SelfLoop openESStep
OpenESKernelSelfLoop = openESSelfLoopProof

OpenESKernelPeriodOne : PeriodOne openESStep
OpenESKernelPeriodOne = periodOne-from-components OpenESKernelIrreducibility OpenESKernelSelfLoop

open import Exotic.ERL.FullCoupled.NoisyNetCoupled

NoisyNetKernelIrreducibility : Irreducible NoisyNetStep
NoisyNetKernelIrreducibility = noisyNetIrreducibilityProof

NoisyNetKernelSelfLoop : SelfLoop NoisyNetStep
NoisyNetKernelSelfLoop = noisyNetSelfLoopProof

NoisyNetKernelPeriodOne : PeriodOne NoisyNetStep
NoisyNetKernelPeriodOne = periodOne-from-components NoisyNetKernelIrreducibility NoisyNetKernelSelfLoop
