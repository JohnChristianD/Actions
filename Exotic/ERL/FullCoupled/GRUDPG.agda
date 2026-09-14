{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUDPG where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; one8
  ; int8Add
  ; int8Mul
  ; CHADOperator
  ; primal
  ; pullback
  ; composeCHAD
  )

-- Finite deterministic actor/critic boundary.
-- The actor is deterministic; the action carrier stays Int8.
-- This is therefore a dyadic finite DPG variant, not the classical
-- continuous-action DPG theorem.
record GRUDPGBoundary (State : Set) : Set₁ where
  constructor gruDPGBoundary
  field
    actor : State → Int8
    critic : State → Int8 → Int8

    -- Critic target keeps the usual max-bootstrap shape:
    -- y = r + gamma * max_a Q(s', a).
    criticBootstrap : Int8 → Int8 → Int8 → Int8
    criticBootstrapLaw :
      ∀ reward gamma maxNext →
        criticBootstrap reward gamma maxNext
        ≡ int8Add reward (int8Mul gamma maxNext)

    -- Finite CHAD action sensitivity and actor sensitivity.
    criticActionPullback : State → Int8 → Int8 → Int8
    actorParameterPullback : State → Int8 → Int8

    -- The actor update is the finite dyadic contraction of the two pullbacks.
    actorUpdate : State → Int8

    actorUpdateDefinition :
      ∀ s →
        actorUpdate s
        ≡ int8Mul
            (criticActionPullback s (actor s) one8)
            (actorParameterPullback s one8)

open GRUDPGBoundary public

-- Exact finite chain-rule form used by the actor update.
finiteDyadicDPGChainLaw :
  ∀ {State : Set} (b : GRUDPGBoundary State) (s : State) →
  actorUpdate b s
  ≡ int8Mul
      (criticActionPullback b s (actor b s) one8)
      (actorParameterPullback b s one8)
finiteDyadicDPGChainLaw b s = actorUpdateDefinition b s

-- The critic max-bootstrap law is independent of the actor update law.
-- Keeping the two equations separate prevents the actor theorem from
-- accidentally replacing the critic target with a policy-evaluated target.
criticMaxBootstrapLaw :
  ∀ {State : Set} (b : GRUDPGBoundary State)
    (reward gamma maxNext : Int8) →
  criticBootstrap b reward gamma maxNext
  ≡ int8Add reward (int8Mul gamma maxNext)
criticMaxBootstrapLaw b = criticBootstrapLaw b

-- The pullback composition law uses the repository's exact finite CHAD
-- composition. This is the reusable representation-side DPG contraction.
finiteDPGPullbackComposition :
  ∀ (outer inner : CHADOperator) (x cotangent : Int8) →
    pullback (composeCHAD outer inner) x cotangent
    ≡ pullback inner x (pullback outer (primal inner x) cotangent)
finiteDPGPullbackComposition outer inner x cotangent = refl
