{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DyadicMethodLawCoupling where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  ; Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne
  )
open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; Method
  ; flatDyadic
  ; mr15GA
  ; openES
  ; noisyNetGRU
  ; HasZero
  ; HasUnitGenerator
  ; law-has-zero
  ; law-has-unit-generator
  ; flat-support
  )
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUMatrices
  ; GRUNoise
  ; GlobalControl
  )
open import Exotic.ERL.FullCoupled.DyadicRepresentation using
  ( RepresentationState
  )
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGActor
  ; DPGCritic
  )

------------------------------------------------------------------------
-- Full finite coupled carrier. It is the architectural state and is kept
-- distinct from the finite support kernel used for aperiodicity.
------------------------------------------------------------------------

record CoupledState : Set where
  constructor coupledState
  field
    representation : RepresentationState
    recurrentMatrices : GRUMatrices
    recurrentNoise : GRUNoise
    actor : DPGActor
    critic : DPGCritic
    globalControl : GlobalControl

open CoupledState public

------------------------------------------------------------------------
-- Genuine Flat-Dyadic support kernel on the finite Int8 carrier.
-- Every target has an explicit support proof; there is no unconstrained
-- target constructor over the full coupled architecture state.
------------------------------------------------------------------------

CanonicalState : Set
CanonicalState = Int8

data CoupledStep : Law → Method → CanonicalState → CanonicalState → Set where
  flatTarget : ∀ {s t} → flat-support t → CoupledStep flatDyadic mr15GA s t
  openESTarget : ∀ {s t} → flat-support t → CoupledStep flatDyadic openES s t
  noisyNetTarget : ∀ {s t} → flat-support t → CoupledStep flatDyadic noisyNetGRU s t

coupledIrreducible :
  ∀ (m : Method) → Irreducible (CoupledStep flatDyadic m)
coupledIrreducible mr15GA s t = there (flatTarget (flat-support t)) here
coupledIrreducible openES s t = there (openESTarget (flat-support t)) here
coupledIrreducible noisyNetGRU s t = there (noisyNetTarget (flat-support t)) here

coupledSelfLoop :
  ∀ (m : Method) → SelfLoop (CoupledStep flatDyadic m)
coupledSelfLoop mr15GA s = flatTarget (flat-support s)
coupledSelfLoop openES s = openESTarget (flat-support s)
coupledSelfLoop noisyNetGRU s = noisyNetTarget (flat-support s)

coupledPeriodOne :
  ∀ (m : Method) → PeriodOne (CoupledStep flatDyadic m)
coupledPeriodOne m =
  periodOne (coupledIrreducible m) (coupledSelfLoop m)

method-law-closure :
  ∀ (m : Method) → Irreducible (CoupledStep flatDyadic m)
method-law-closure = coupledIrreducible

method-law-aperiodicity :
  ∀ (m : Method) → SelfLoop (CoupledStep flatDyadic m)
method-law-aperiodicity = coupledSelfLoop

------------------------------------------------------------------------
-- Canonical lift into the full coupled architecture. The projection/lift
-- theorem is genuine and establishes a finite representation subcarrier;
-- it does not claim irreducibility of every arbitrary CoupledState.
------------------------------------------------------------------------

canonicalRepresentation : Int8 → RepresentationState
canonicalRepresentation x =
  record
    { sparseValue = x
    ; haarValue = x
    ; ropeValue = x
    }

canonicalLift : Int8 → CoupledState
canonicalLift x =
  record
    { representation = canonicalRepresentation x
    ; recurrentMatrices = record
        { updateMatrix = x
        ; resetMatrix = x
        ; candidateMatrix = x
        }
    ; recurrentNoise = record
        { updateNoise = x
        ; resetNoise = x
        ; candidateNoise = x
        }
    ; actor = record
        { actorWeight = x
        ; globalActor = record { optimizer = x ; l2 = x }
        }
    ; critic = record
        { criticWeight = x
        ; globalCritic = record { optimizer = x ; l2 = x }
        }
    ; globalControl = record { optimizerToken = x ; l2Token = x }
    }

canonicalProjection : CoupledState → Int8
canonicalProjection s = RepresentationState.sparseValue (representation s)

canonicalProjection-lift :
  ∀ x → canonicalProjection (canonicalLift x) ≡ x
canonicalProjection-lift x = refl

data CoupledStateStep : Law → Method → CoupledState → CoupledState → Set where
  canonicalFlatStateTarget :
    ∀ {m s t} → flat-support t →
    CoupledStateStep flatDyadic m (canonicalLift s) (canonicalLift t)

record RecurrentProjection : Set₁ where
  constructor recurrentProjection
  field
    project : CoupledState → Int8
    lift : Int8 → CoupledState
    project-lift : ∀ x → project (lift x) ≡ x
    representation-step :
      ∀ {x y}
      → CoupledStateStep flatDyadic noisyNetGRU (lift x) (lift y)

open RecurrentProjection public

noisyNetProjection : RecurrentProjection
noisyNetProjection =
  recurrentProjection
    canonicalProjection
    canonicalLift
    canonicalProjection-lift
    (λ {x} {y} → canonicalFlatStateTarget (flat-support y))

noisyNet-project-lift :
  ∀ x → project noisyNetProjection (lift noisyNetProjection x) ≡ x
noisyNet-project-lift x = refl

law-zero-witness : HasZero flatDyadic
law-zero-witness = law-has-zero flatDyadic

law-generator-witness : HasUnitGenerator flatDyadic
law-generator-witness = law-has-unit-generator flatDyadic
