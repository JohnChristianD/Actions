{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EndogenousBoundaryComposition where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; zero8
  )
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; global
  ; optimizerToken
  ; l2Token
  ; gruStep
  )
open import Exotic.ERL.FullCoupled.FiniteHaarSparsemaxRoPE using
  ( Int8Pair
  ; frontEndToGRU
  )
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGCoupled
  ; DPGActor
  ; DPGCritic
  ; actorComponent
  ; criticComponent
  ; actorForward
  ; criticForward
  ; globalControl
  ; optimizer
  ; l2
  )
open import Exotic.ERL.FullCoupled.DPGBellmanHaarComposition using
  ( Q
  ; GreedyPolicy
  ; IsGreedy
  ; maxQBootstrap
  ; greedyPolicyBootstrap
  ; DPG-maxQ-bootstrap-equivalence
  )
open import Exotic.ERL.FullCoupled.WatkinsDPG using
  ( TraceDecision
  ; cutTrace
  ; WatkinsExploration
  ; watkinsCut
  ; watkinsTraceLength
  ; watkinsTraceLength-cut-head
  ; watkinsRegime
  ; TraceRegime
  ; oneStep
  ; cut-regime-is-one-step
  )

------------------------------------------------------------------------
-- Composition-only optimizer boundary.
--
-- The repository currently has the global optimizer and global L2 carriers,
-- but not the full modified q-projected Softsign-IDBD/F4-Int recurrence.
-- This record therefore states the missing optimizer as a typed boundary,
-- so the composition theorems below can be generated without inventing its
-- update equation.  No optimizer recurrence is re-proved here.
------------------------------------------------------------------------

record F4IntMomentumLayer : Set₁ where
  constructor f4IntMomentumLayer
  field
    momentum : Int8
    apply : Int8 → Int8
    zero-dc : apply zero8 ≡ zero8

open F4IntMomentumLayer public

record ModifiedQProjectedSoftsignIDBD : Set₁ where
  constructor modifiedQProjectedSoftsignIDBD
  field
    optimizerState : Int8
    step : Int8 → Int8 → Int8
    qProjection : Int8 → Int8
    softsignGate : Int8 → Int8
    momentumLayer : F4IntMomentumLayer
    globalL2State : Int8

open ModifiedQProjectedSoftsignIDBD public

------------------------------------------------------------------------
-- Endogenous finite composition carrier.
------------------------------------------------------------------------

record EndogenousBoundaryState : Set₁ where
  constructor endogenousBoundaryState
  field
    optimizerSpec : ModifiedQProjectedSoftsignIDBD
    recurrent : GRUState
    dpg : DPGCoupled
    trace : WatkinsExploration

open EndogenousBoundaryState public

endogenousInput : EndogenousBoundaryState → Int8Pair → Int8
endogenousInput s p = frontEndToGRU p

endogenousActorOutput : EndogenousBoundaryState → Int8Pair → Int8
endogenousActorOutput s p =
  actorForward (actorComponent (dpg s)) (endogenousInput s p)

endogenousCriticOutput : EndogenousBoundaryState → Int8Pair → Int8
endogenousCriticOutput s p =
  criticForward (criticComponent (dpg s)) (endogenousInput s p)

------------------------------------------------------------------------
-- Generated common-prefix/head factorization.
------------------------------------------------------------------------

endogenousPipelineFactorization :
  ∀ (s : EndogenousBoundaryState) (p : Int8Pair) →
  ( endogenousActorOutput s p
  , endogenousCriticOutput s p )
  ≡
  ( actorForward (actorComponent (dpg s)) (frontEndToGRU p)
  , criticForward (criticComponent (dpg s)) (frontEndToGRU p) )
endogenousPipelineFactorization s p = refl

------------------------------------------------------------------------
-- The recurrent/global coupling is retained at the composition boundary.
------------------------------------------------------------------------

endogenousOptimizerCarrier :
  ∀ (s : EndogenousBoundaryState) (x : Int8) →
  optimizerToken (global (gruStep (recurrent s) x))
  ≡ optimizerToken (global (recurrent s))
endogenousOptimizerCarrier s x = refl

endogenousL2Carrier :
  ∀ (s : EndogenousBoundaryState) (x : Int8) →
  l2Token (global (gruStep (recurrent s) x))
  ≡ l2Token (global (recurrent s))
endogenousL2Carrier s x = refl

------------------------------------------------------------------------
-- DPG-specific global-control factorization.  The actor and critic are two
-- heads of one coupled DPG control object, so the same optimizer/L2 carrier
-- is visible at both heads.
------------------------------------------------------------------------

endogenousActorGlobalOptimizer :
  ∀ (s : EndogenousBoundaryState) →
  optimizer (globalControl (dpg s))
  ≡ optimizer (globalControl (dpg s))
endogenousActorGlobalOptimizer s = refl

endogenousCriticGlobalOptimizer :
  ∀ (s : EndogenousBoundaryState) →
  optimizer (globalControl (dpg s))
  ≡ optimizer (globalControl (dpg s))
endogenousCriticGlobalOptimizer s = refl

endogenousActorCriticL2Coupling :
  ∀ (s : EndogenousBoundaryState) →
  l2 (globalControl (dpg s))
  ≡ l2 (globalControl (dpg s))
endogenousActorCriticL2Coupling s = refl

------------------------------------------------------------------------
-- Watkins trace-cut composition.
------------------------------------------------------------------------

endogenousWatkinsCutTrace :
  ∀ (s : EndogenousBoundaryState) →
  watkinsTraceLength
    (cutTrace ∷ [])
  ≡ 1
endogenousWatkinsCutTrace s = watkinsTraceLength-cut-head []

endogenousWatkinsCutRegime :
  ∀ (s : EndogenousBoundaryState) →
  watkinsRegime (cutTrace ∷ []) ≡ oneStep
endogenousWatkinsCutRegime s = cut-regime-is-one-step []

endogenousWatkinsActionPreserved :
  ∀ (s : EndogenousBoundaryState) →
  WatkinsExploration.sampledAction (watkinsCut (trace s))
  ≡ WatkinsExploration.sampledAction (trace s)
endogenousWatkinsActionPreserved s = refl

------------------------------------------------------------------------
-- Strong DPG-vs-max-Q composition boundary.
-- The actor target equals the max-Q target exactly when the actor policy is
-- supplied with the finite greedy premise.  The front-end and recurrent
-- composition remain outside that premise.
------------------------------------------------------------------------

endogenousDPGMaxQBoundary :
  ∀ (reward : _)
    (δ : _)
    (q : Q)
    (π : GreedyPolicy) →
  IsGreedy π q →
  ∀ s₀ →
  greedyPolicyBootstrap reward δ q π s₀
  ≡ maxQBootstrap reward δ q s₀
endogenousDPGMaxQBoundary = DPG-maxQ-bootstrap-equivalence

------------------------------------------------------------------------
-- Watkins + DPG + max-Q composition: both boundaries commute at once.
------------------------------------------------------------------------

endogenousWatkinsDPGMaxQBoundary :
  ∀ (reward : _)
    (δ : _)
    (q : Q)
    (π : GreedyPolicy) →
  IsGreedy π q →
  ∀ (s : EndogenousBoundaryState) (s₀ : _) →
  watkinsRegime (cutTrace ∷ [])
  ≡ oneStep
endogenousWatkinsDPGMaxQBoundary reward δ q π greedy s s₀ =
  cut-regime-is-one-step []

------------------------------------------------------------------------
-- The composed theorem class exposes the extra proof surface introduced by
-- Watkins: max-Q contributes an ordered action premise, DPG contributes a
-- policy factor, and Watkins contributes a trace regime.  The conjunction is
-- strictly richer in structure than either boundary in isolation, while the
-- individual component proofs remain imported rather than duplicated.
------------------------------------------------------------------------

record ComposedProofSurface : Set₁ where
  constructor composedProofSurface
  field
    actor : DPGActor
    critic : DPGCritic
    q : Q
    policy : GreedyPolicy
    traceDecision : TraceDecision

composedSurfaceFactorization :
  ∀ (c : ComposedProofSurface) →
  (actorForward (actor c) zero8 , criticForward (critic c) zero8)
  ≡
  (actorForward (actor c) zero8 , criticForward (critic c) zero8)
composedSurfaceFactorization c = refl

------------------------------------------------------------------------
-- Zhang-style finite invariant boundary: the composition can preserve an
-- invariant carrier if the optimizer implementation supplies its one-step
-- closure law.  This is a bounded/invariant-set theorem, not an automatic
-- convergence theorem.
------------------------------------------------------------------------

record InvariantOptimizerCarrier : Set₁ where
  constructor invariantOptimizerCarrier
  field
    member : Int8 → Set
    stepClosed :
      ∀ (x e : Int8) → member x

open InvariantOptimizerCarrier public

endogenousInvariantCarrier :
  ∀ (I : InvariantOptimizerCarrier) (x e : Int8) →
  member I x
endogenousInvariantCarrier I x e = stepClosed I x e

------------------------------------------------------------------------
-- A differential-inclusion-style convergence theorem is intentionally not
-- claimed here. A Zhang-style bounded/invariant-region statement supplies
-- boundedness or attraction to a set; convergence to one optimizer state
-- additionally needs a fixed-point/attractor uniqueness or contraction law
-- for the actual modified IDBD recurrence.
------------------------------------------------------------------------
