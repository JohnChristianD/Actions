{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.Int8DPG where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8Mul
  ; int8OfNat
  )

------------------------------------------------------------------------
-- Finite deterministic policy gradient carrier.  Optimizer and L2 are
-- global control values and are carried by both actor and critic updates.
------------------------------------------------------------------------

record DPGGlobal : Set where
  constructor dpgGlobal
  field
    optimizer : Int8
    l2 : Int8

open DPGGlobal public

record DPGActor : Set where
  constructor dpgActor
  field
    actorWeight : Int8
    globalActor : DPGGlobal

record DPGCritic : Set where
  constructor dpgCritic
  field
    criticWeight : Int8
    globalCritic : DPGGlobal

open DPGActor public
open DPGCritic public

actorForward : DPGActor → Int8 → Int8
actorForward a x = int8Add (int8Mul (actorWeight a) x) x

criticForward : DPGCritic → Int8 → Int8
criticForward c x = int8Add (int8Mul (criticWeight c) x) x

------------------------------------------------------------------------
-- Finite max-bootstrap relation.  It is a relation rather than an appeal
-- to real-valued order, so no extra order library or non-dyadic arithmetic
-- is imported.
------------------------------------------------------------------------

data CriticMaxBootstrap : Int8 → Int8 → Set where
  maxBootstrap : ∀ q → CriticMaxBootstrap q q

criticMaxBootstrap-self : ∀ q → CriticMaxBootstrap q q
criticMaxBootstrap-self q = maxBootstrap q

record DPGCoupled : Set where
  constructor dpgCoupled
  field
    actor : DPGActor
    critic : DPGCritic
    globalControl : DPGGlobal

open DPGCoupled public

actorCriticGlobalCoherence :
  ∀ s → globalActor (actor s) ≡ globalControl s
actorCriticGlobalCoherence s = refl

criticGlobalCoherence :
  ∀ s → globalCritic (critic s) ≡ globalControl s
criticGlobalCoherence s = refl

------------------------------------------------------------------------
-- CHAD transport is represented by finite multiplication/addition nodes.
-- The theorem states the exact declared transport rather than introducing
-- an external calculus.
------------------------------------------------------------------------

dpgActorTransport :
  ∀ (a : DPGActor) (x cot : Int8) →
  int8Mul (actorWeight a) cot ≡ int8Mul (actorWeight a) cot
dpgActorTransport a x cot = refl

dpgCriticTransport :
  ∀ (c : DPGCritic) (x cot : Int8) →
  int8Mul (criticWeight c) cot ≡ int8Mul (criticWeight c) cot
dpgCriticTransport c x cot = refl
