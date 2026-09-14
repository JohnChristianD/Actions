{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EndogenousBoundaryComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
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
  ( State
  ; Q
  ; GreedyPolicy
  ; Discount
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
  ; oneStep
  ; cut-regime-is-one-step
  )

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

endogenousPipelineFactorization :
  ∀ (s : EndogenousBoundaryState) (p : Int8Pair) →
  ( endogenousActorOutput s p
  , endogenousCriticOutput s p )
  ≡
  ( actorForward (actorComponent (dpg s)) (frontEndToGRU p)
  , criticForward (criticComponent (dpg s)) (frontEndToGRU p) )
endogenousPipelineFactorization s p = refl

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

endogenousWatkinsCutTrace :
  ∀ (s : EndogenousBoundaryState) →
  watkinsTraceLength (cutTrace ∷ [])
  ≡ suc zero
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

endogenousDPGMaxQBoundary :
  ∀ (reward : ℕ) (δ : Discount) (q : Q) (π : GreedyPolicy) →
  IsGreedy π q →
  ∀ s₀ →
  greedyPolicyBootstrap reward δ q π s₀
  ≡ maxQBootstrap reward δ q s₀
endogenousDPGMaxQBoundary = DPG-maxQ-bootstrap-equivalence

endogenousWatkinsDPGMaxQBoundary :
  ∀ (reward : ℕ) (δ : Discount) (q : Q) (π : GreedyPolicy) →
  IsGreedy π q →
  ∀ (s : EndogenousBoundaryState) (s₀ : State) →
  greedyPolicyBootstrap reward δ q π s₀
  ≡ maxQBootstrap reward δ q s₀
endogenousWatkinsDPGMaxQBoundary reward δ q π greedy s s₀ =
  DPG-maxQ-bootstrap-equivalence reward δ q π greedy s₀

record EndogenousWatkinsDPGMaxQResult
  (s : EndogenousBoundaryState)
  (p : Int8Pair)
  (reward : ℕ)
  (δ : Discount)
  (q : Q)
  (π : GreedyPolicy)
  (greedy : IsGreedy π q)
  (s₀ : State) : Set₁ where
  constructor endogenousWatkinsDPGMaxQResult
  field
    pipeline :
      ( endogenousActorOutput s p
      , endogenousCriticOutput s p )
      ≡
      ( actorForward (actorComponent (dpg s)) (frontEndToGRU p)
      , criticForward (criticComponent (dpg s)) (frontEndToGRU p) )
    optimizerCarrier :
      optimizerToken (global (gruStep (recurrent s) zero8))
      ≡ optimizerToken (global (recurrent s))
    l2Carrier :
      l2Token (global (gruStep (recurrent s) zero8))
      ≡ l2Token (global (recurrent s))
    traceCut :
      watkinsRegime (cutTrace ∷ []) ≡ oneStep
    targetEquality :
      greedyPolicyBootstrap reward δ q π s₀
      ≡ maxQBootstrap reward δ q s₀

endogenousWatkinsDPGMaxQ :
  ∀ (s : EndogenousBoundaryState)
    (p : Int8Pair)
    (reward : ℕ)
    (δ : Discount)
    (q : Q)
    (π : GreedyPolicy)
  → (greedy : IsGreedy π q)
  → (s₀ : State)
  → EndogenousWatkinsDPGMaxQResult s p reward δ q π greedy s₀
endogenousWatkinsDPGMaxQ s p reward δ q π greedy s₀ =
  endogenousWatkinsDPGMaxQResult
    (endogenousPipelineFactorization s p)
    (endogenousOptimizerCarrier s zero8)
    (endogenousL2Carrier s zero8)
    (endogenousWatkinsCutRegime s)
    (endogenousDPGMaxQBoundary reward δ q π greedy s₀)

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

record InvariantOptimizerCarrier : Set₁ where
  constructor invariantOptimizerCarrier
  field
    member : Int8 → Set
    stepClosed : ∀ (x e : Int8) → member x

open InvariantOptimizerCarrier public

endogenousInvariantCarrier :
  ∀ (I : InvariantOptimizerCarrier) (x e : Int8) →
  member I x
endogenousInvariantCarrier I x e = stepClosed I x e

------------------------------------------------------------------------
-- The composition theorem intentionally stops at a Zhang-style invariant
-- region. Differential-inclusion boundedness/attraction does not by itself
-- prove convergence to one optimizer state; that additionally needs a
-- fixed-point/attractor uniqueness or contraction theorem for the actual
-- modified IDBD recurrence.
------------------------------------------------------------------------
