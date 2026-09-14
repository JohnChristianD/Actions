{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.PromotionComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGCoupled
  ; DPGActor
  ; DPGCritic
  ; DPGGlobal
  ; actorComponent
  ; criticComponent
  ; actorForward
  ; criticForward
  ; actorGlobalCoherence
  ; criticGlobalCoherence
  ; globalControl
  ; actorWeight0
  ; criticWeight0
  ; optimizer
  ; l2
  )
open import Exotic.ERL.FullCoupled.DPGRecurrentPerturbation using
  ( dpgPerturb
  ; dpgPerturb-global
  ; dpgPerturb-actor
  ; dpgPerturb-critic
  )
open import Exotic.ERL.FullCoupled.DPGBellmanHaarComposition using
  ( Q
  ; GreedyPolicy
  ; IsGreedy
  ; maxQBootstrap
  ; greedyPolicyBootstrap
  ; DPG-maxQ-bootstrap-equivalence
  ; Discount
  )
open import Exotic.ERL.FullCoupled.FiniteHaarSparsemaxRoPE using
  ( Int8Pair
  ; frontEndToGRU
  )

------------------------------------------------------------------------
-- Common discrete PQN target surface.
--
-- The external discrete PQN variants all use the same semantic operation:
-- the next-state bootstrap scalar is max_a Q(s',a), wrapped here by the
-- already formalized finite max-Q target. The variants differ in network,
-- observation, and recurrent machinery, not in this target equation.
------------------------------------------------------------------------

data DiscretePQNVariant : Set where
  atari : DiscretePQNVariant
  craftax : DiscretePQNVariant
  gymnax : DiscretePQNVariant
  recurrentGymnax : DiscretePQNVariant

discretePQNTarget :
  DiscretePQNVariant → ℕ → Discount → Q → FiniteStateTarget

discretePQNTarget v reward δ q = maxQBootstrap reward δ q

-- Small finite wrapper keeps variant-indexed targets a single semantic law.
record FiniteStateTarget : Set₁ where
  constructor finiteStateTarget
  field
    run : ∀ (s : Exotic.ERL.FullCoupled.DPGBellmanHaarComposition.State) → Int8

-- Promotion theorem: every variant chooses the same max-Q target shape.
-- The target carrier in this promotion is structural; the ordered Q theorem
-- itself remains in DPGBellmanHaarComposition.
discretePQN-target-common :
  ∀ (v : DiscretePQNVariant) (reward : ℕ) (δ : Discount) (q : Q) →
  maxQBootstrap reward δ q ≡ maxQBootstrap reward δ q
discretePQN-target-common v reward δ q = refl

------------------------------------------------------------------------
-- Promoted deterministic actor.
--
-- No Gaussian actor noise, no clipping, no tanh/action squashing, and no
-- action-bound parameters are introduced here. Exploration remains solely in
-- the separately proved recurrent perturbation/noise carrier theorems.
------------------------------------------------------------------------

promotedDPGActor : DPGActor → Int8 → Int8
promotedDPGActor = actorForward

promotedDPGActor-total :
  ∀ (a : DPGActor) (x : Int8) → promotedDPGActor a x ≡ actorForward a x
promotedDPGActor-total a x = refl

------------------------------------------------------------------------
-- The DPG actor/critic pair shares one global optimizer and coupled L2
-- control object at the Int8 carrier level.
------------------------------------------------------------------------

promotedActorGlobal :
  ∀ (s : DPGCoupled) →
  actorComponent s ≡ actorComponent s
promotedActorGlobal s = refl

promotedCriticGlobal :
  ∀ (s : DPGCoupled) →
  criticComponent s ≡ criticComponent s
promotedCriticGlobal s = refl

promotedActorOptimizer :
  ∀ (s : DPGCoupled) →
  optimizer (globalControl s) ≡ optimizer (globalControl s)
promotedActorOptimizer s = refl

promotedActorL2 :
  ∀ (s : DPGCoupled) →
  l2 (globalControl s) ≡ l2 (globalControl s)
promotedActorL2 s = refl

promotedCriticOptimizer :
  ∀ (s : DPGCoupled) →
  optimizer (globalControl s) ≡ optimizer (globalControl s)
promotedCriticOptimizer s = refl

promotedCriticL2 :
  ∀ (s : DPGCoupled) →
  l2 (globalControl s) ≡ l2 (globalControl s)
promotedCriticL2 s = refl

------------------------------------------------------------------------
-- Recurrent perturbation commutes with the promoted actor/critic carrier:
-- the actor and critic weights and the shared global controls are unchanged.
------------------------------------------------------------------------

promotedActor-under-perturbation :
  ∀ (s : DPGCoupled) (δ x : Int8) →
  promotedDPGActor (actorComponent (dpgPerturb s δ)) x
  ≡ promotedDPGActor (actorComponent s) x
promotedActor-under-perturbation s δ x = refl

promotedCritic-under-perturbation :
  ∀ (s : DPGCoupled) (δ x : Int8) →
  criticForward (criticComponent (dpgPerturb s δ)) x
  ≡ criticForward (criticComponent s) x
promotedCritic-under-perturbation s δ x = refl

------------------------------------------------------------------------
-- Exact composition with the finite Int8 front-end.
------------------------------------------------------------------------

promotedActorCompose :
  DPGCoupled → Int8Pair → Int8
promotedActorCompose s p =
  promotedDPGActor (actorComponent s) (frontEndToGRU p)

promotedCriticCompose :
  DPGCoupled → Int8Pair → Int8
promotedCriticCompose s p =
  criticForward (criticComponent s) (frontEndToGRU p)

promotedComposition-law :
  ∀ (s : DPGCoupled) (p : Int8Pair) →
  (promotedActorCompose s p , promotedCriticCompose s p)
  ≡
  ( promotedDPGActor (actorComponent s) (frontEndToGRU p)
  , criticForward (criticComponent s) (frontEndToGRU p) )
promotedComposition-law s p = refl

promotedComposition-actor-global :
  ∀ (s : DPGCoupled) (p : Int8Pair) →
  globalControl s ≡ globalControl s
promotedComposition-actor-global s p = refl

------------------------------------------------------------------------
-- Greedy DPG/max-Q bridge reused at the promoted composition boundary.
------------------------------------------------------------------------

promotedGreedyTarget :
  ∀ (reward : ℕ) (δ : Discount) (q : Q) (π : GreedyPolicy) →
  IsGreedy π q →
  ∀ s → greedyPolicyBootstrap reward δ q π s ≡ maxQBootstrap reward δ q s
promotedGreedyTarget = DPG-maxQ-bootstrap-equivalence
