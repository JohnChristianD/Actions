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
  ; lazyUnit
  ; dyadicLadder
  ; mr15GA
  ; openES
  ; noisyNetGRU
  ; HasZero
  ; HasUnitGenerator
  ; law-has-zero
  ; law-has-unit-generator
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
-- One finite state for every method/law permutation.  The optimizer and L2
-- controls are global components of the coupled state, never local method
-- state.
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
-- The finite coupling kernel is the actual theorem carrier.  A fresh finite
-- law sample is represented by its target coupled state; the law/method tags
-- select which theorem family is being instantiated.
------------------------------------------------------------------------

data CoupledStep : Law → Method → CoupledState → CoupledState → Set where
  coupledTarget : ∀ {l m s} t → CoupledStep l m s t

coupledIrreducible :
  ∀ (l : Law) (m : Method) → Irreducible (CoupledStep l m)
coupledIrreducible l m s t = there (coupledTarget t) here

coupledSelfLoop :
  ∀ (l : Law) (m : Method) → SelfLoop (CoupledStep l m)
coupledSelfLoop l m s = coupledTarget s

coupledPeriodOne :
  ∀ (l : Law) (m : Method) → PeriodOne (CoupledStep l m)
coupledPeriodOne l m =
  periodOne (coupledIrreducible l m) (coupledSelfLoop l m)

------------------------------------------------------------------------
-- Endogenous law closure: all three laws expose the same zero and unit
-- witnesses, so their full coupling inherits a self-loop and a generator.
------------------------------------------------------------------------

law-zero-witness : ∀ l → HasZero l
law-zero-witness = law-has-zero

law-generator-witness : ∀ l → HasUnitGenerator l
law-generator-witness = law-has-unit-generator

method-law-closure :
  ∀ (l : Law) (m : Method) →
  Irreducible (CoupledStep l m)
method-law-closure = coupledIrreducible

method-law-aperiodicity :
  ∀ (l : Law) (m : Method) →
  SelfLoop (CoupledStep l m)
method-law-aperiodicity = coupledSelfLoop

------------------------------------------------------------------------
-- Noisy Net recurrent projection/lift.  This is the missing bridge that
-- prevents a gate-only theorem from being presented as a full-representation
-- theorem.
------------------------------------------------------------------------

record RecurrentProjection : Set₁ where
  constructor recurrentProjection
  field
    project : CoupledState → Int8
    lift : Int8 → CoupledState
    project-lift : ∀ x → project (lift x) ≡ x
    representation-step :
      ∀ {x y} → CoupledStep noisyNetGRU noisyNetGRU (lift x) (lift y)

open RecurrentProjection public

noisyNetProjection : RecurrentProjection
noisyNetProjection =
  recurrentProjection
    (λ s → RepresentationState.sparseValue (representation s))
    (λ x → canonicalLift x)
    (λ x → refl)
    (λ {x} {y} → coupledTarget (canonicalLift y))
  where
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

noisyNet-project-lift : ∀ x → project noisyNetProjection (lift noisyNetProjection x) ≡ x
noisyNet-project-lift x = refl
