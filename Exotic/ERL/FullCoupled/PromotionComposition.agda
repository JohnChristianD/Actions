{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.PromotionComposition where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGCoupled
  ; DPGActor
  ; actorComponent
  ; criticComponent
  ; actorForward
  ; criticForward
  ; actorGlobalCoherence
  ; criticGlobalCoherence
  ; globalControl
  ; globalActor
  ; globalCritic
  ; optimizer
  ; l2
  )
open import Exotic.ERL.FullCoupled.DPGRecurrentPerturbation using
  ( dpgPerturb
  )
open import Exotic.ERL.FullCoupled.DPGBellmanHaarComposition using
  ( State
  ; Q
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
-- The inspected discrete PQN variants use the same semantic bootstrap:
-- the next-state scalar is max_a Q(s',a), with λ-return machinery wrapped
-- around that bootstrap. Their architectures and recurrent handling differ,
-- but their target operator is the same max-Q operator.
------------------------------------------------------------------------

data DiscretePQNVariant : Set where
  atari : DiscretePQNVariant
  craftax : DiscretePQNVariant
  gymnax : DiscretePQNVariant
  recurrentGymnax : DiscretePQNVariant

discretePQNTarget :
  DiscretePQNVariant → ℕ → Discount → Q → State → ℕ
discretePQNTarget v reward δ q s = maxQBootstrap reward δ q s

discretePQN-target-common :
  ∀ (v : DiscretePQNVariant) (reward : ℕ) (δ : Discount) (q : Q)
    (s : State) →
  discretePQNTarget v reward δ q s ≡ maxQBootstrap reward δ q s
discretePQN-target-common v reward δ q s = refl

------------------------------------------------------------------------
-- Promoted deterministic actor.
--
-- No Gaussian actor noise, no clipping, no tanh/action squashing, and no
-- action-bound parameters are introduced here. Exploration stays in the
-- separately canonical recurrent perturbation/noise carrier theorems.
------------------------------------------------------------------------

promotedDPGActor : DPGActor → Int8 → Int8
promotedDPGActor = actorForward

promotedDPGActor-total :
  ∀ (a : DPGActor) (x : Int8) → promotedDPGActor a x ≡ actorForward a x
promotedDPGActor-total a x = refl

------------------------------------------------------------------------
-- Global optimizer and coupled L2 are shared by actor and critic.
------------------------------------------------------------------------

promotedActorOptimizer :
  ∀ (s : DPGCoupled) →
  optimizer (globalActor (actorComponent s))
  ≡ optimizer (globalControl s)
promotedActorOptimizer s = cong optimizer (actorGlobalCoherence s)

promotedActorL2 :
  ∀ (s : DPGCoupled) →
  l2 (globalActor (actorComponent s))
  ≡ l2 (globalControl s)
promotedActorL2 s = cong l2 (actorGlobalCoherence s)

promotedCriticOptimizer :
  ∀ (s : DPGCoupled) →
  optimizer (globalCritic (criticComponent s))
  ≡ optimizer (globalControl s)
promotedCriticOptimizer s = cong optimizer (criticGlobalCoherence s)

promotedCriticL2 :
  ∀ (s : DPGCoupled) →
  l2 (globalCritic (criticComponent s))
  ≡ l2 (globalControl s)
promotedCriticL2 s = cong l2 (criticGlobalCoherence s)

------------------------------------------------------------------------
-- Recurrent perturbation commutes with the promoted actor/critic carrier:
-- actor and critic weights/global controls are unchanged by the perturbation.
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

------------------------------------------------------------------------
-- The promoted actor/critic composition preserves the same global controls
-- because the two heads are constructed from one DPGCoupled globalControl.
------------------------------------------------------------------------

promotedComposition-actor-optimizer :
  ∀ (s : DPGCoupled) (p : Int8Pair) →
  optimizer (globalActor (actorComponent s))
  ≡ optimizer (globalControl s)
promotedComposition-actor-optimizer s p = promotedActorOptimizer s

promotedComposition-actor-L2 :
  ∀ (s : DPGCoupled) (p : Int8Pair) →
  l2 (globalActor (actorComponent s))
  ≡ l2 (globalControl s)
promotedComposition-actor-L2 s p = promotedActorL2 s

promotedComposition-critic-optimizer :
  ∀ (s : DPGCoupled) (p : Int8Pair) →
  optimizer (globalCritic (criticComponent s))
  ≡ optimizer (globalControl s)
promotedComposition-critic-optimizer s p = promotedCriticOptimizer s

promotedComposition-critic-L2 :
  ∀ (s : DPGCoupled) (p : Int8Pair) →
  l2 (globalCritic (criticComponent s))
  ≡ l2 (globalControl s)
promotedComposition-critic-L2 s p = promotedCriticL2 s

------------------------------------------------------------------------
-- Greedy DPG/max-Q bridge reused at the promoted composition boundary.
------------------------------------------------------------------------

promotedGreedyTarget :
  ∀ (reward : ℕ) (δ : Discount) (q : Q) (π : GreedyPolicy) →
  IsGreedy π q →
  ∀ s → greedyPolicyBootstrap reward δ q π s ≡ maxQBootstrap reward δ q s
promotedGreedyTarget = DPG-maxQ-bootstrap-equivalence
