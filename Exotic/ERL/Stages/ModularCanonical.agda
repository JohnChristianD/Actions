{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.ModularCanonical where

open import Agda.Builtin.Unit using (⊤; tt)
open import Exotic.ERL.Stages.Stage08_Integration
open import Exotic.ERL.Stages.Stage09_FiniteLocalConvergence

modularCanonicalClosure : ⊤
modularCanonicalClosure = proofDAGConnected

modularCoupledWitness : ∀ {s : Stage08State} → CoupledIntegrationCertificate s
modularCoupledWitness {s} = combinedCoupledTheorem s

modularFiniteLocalConvergence :
  ∀ c s →
  reachesWithin
    (CoupledRankCertificate.terminal c)
    (CoupledRankCertificate.jointStep c)
    (CoupledRankCertificate.rank c s)
    s
modularFiniteLocalConvergence c s = finiteLocalConvergenceByRanking c s
