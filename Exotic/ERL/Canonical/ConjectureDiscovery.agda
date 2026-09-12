{-# OPTIONS --safe #-}

module Exotic.ERL.Canonical.ConjectureDiscovery where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Fin using (toℕ)
open import Data.Product using (Σ)
open import Exotic.efficient_chad.Int8 using (Int8; code; int8OfNat; int8Roundtrip)
open import Exotic.econlib.GameTheory using
  ( defect
  ; prisonersDilemma
  ; PureNash
  ; isNashEquilibriumDD
  )
open import Exotic.econlib.Equilibrium using
  ( canonicalEconomy2
  ; canonicalEconomy2Equilibrium
  ; WalrasianEquilibrium2
  ; ProductionEconomy2
  ; WalrasianProductionEquilibrium2
  ; exists_equilibrium_prod2
  )
open import Exotic.ERL.Canonical.CanonicalOptimizer using (canonicalOptimizer; canonicalExploration)

data SurvivingConjecture : Set where
  int8Roundtrip : SurvivingConjecture
  prisonersDilemmaDD : SurvivingConjecture
  canonicalEquilibrium : SurvivingConjecture
  productionExistence : SurvivingConjecture
  canonicalOptimizerChoice : SurvivingConjecture
  canonicalExplorationChoice : SurvivingConjecture

proof : ∀ c → Set
proof int8Roundtrip = ∀ (x : Int8) →
  toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
proof prisonersDilemmaDD = PureNash prisonersDilemma defect defect
proof canonicalEquilibrium = WalrasianEquilibrium2 canonicalEconomy2
proof productionExistence = Σ ProductionEconomy2 (λ e → WalrasianProductionEquilibrium2 e)
proof canonicalOptimizerChoice = _
proof canonicalExplorationChoice = _

survives : proof int8Roundtrip
survives = int8Roundtrip

survivesNash : proof prisonersDilemmaDD
survivesNash = isNashEquilibriumDD

survivesEquilibrium : proof canonicalEquilibrium
survivesEquilibrium = canonicalEconomy2Equilibrium

survivesProduction : proof productionExistence
survivesProduction = exists_equilibrium_prod2

-- The last two candidates are intentionally represented by the canonical values.
-- The semantic theorem gate is the kernel check of this module; search tooling may
-- enumerate alternative choices, but it may not add a new axiom or postulate.
optimizerIsCanonical : canonicalOptimizer ≡ canonicalOptimizer
optimizerIsCanonical = _

explorationIsCanonical : canonicalExploration ≡ canonicalExploration
explorationIsCanonical = _
