module Exotic.ERL.Stages.ModularCanonical where

open import Agda.Builtin.Unit using (⊤; tt)
open import Exotic.ERL.Stages.Stage08_Integration

modularCanonicalClosure : ⊤
modularCanonicalClosure = proofDAGConnected

modularCoupledWitness : ∀ {s : Stage08State} → CoupledIntegrationCertificate s
modularCoupledWitness {s} = combinedCoupledTheorem s
