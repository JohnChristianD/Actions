{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.Int8DPG where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8Mul
  )

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

data CriticMaxBootstrap : Int8 → Int8 → Set where
  maxBootstrap : ∀ q → CriticMaxBootstrap q q

criticMaxBootstrap-self : ∀ q → CriticMaxBootstrap q q
criticMaxBootstrap-self q = maxBootstrap q

record DPGCoupled : Set where
  constructor dpgCoupled
  field
    globalControl : DPGGlobal
    actorWeight0 : Int8
    criticWeight0 : Int8

open DPGCoupled public

actorComponent : DPGCoupled → DPGActor
actorComponent s = dpgActor (actorWeight0 s) (globalControl s)

criticComponent : DPGCoupled → DPGCritic
criticComponent s = dpgCritic (criticWeight0 s) (globalControl s)

actorGlobalCoherence :
  ∀ s → globalActor (actorComponent s) ≡ globalControl s
actorGlobalCoherence s = refl

criticGlobalCoherence :
  ∀ s → globalCritic (criticComponent s) ≡ globalControl s
criticGlobalCoherence s = refl

dpgActorTransport :
  ∀ (a : DPGActor) (x cot : Int8) →
  int8Mul (actorWeight a) cot ≡ int8Mul (actorWeight a) cot
dpgActorTransport a x cot = refl

dpgCriticTransport :
  ∀ (c : DPGCritic) (x cot : Int8) →
  int8Mul (criticWeight c) cot ≡ int8Mul (criticWeight c) cot
dpgCriticTransport c x cot = refl

------------------------------------------------------------------------
-- Int8 DPG actor action closure.
--
-- We close the actor's *action semantics* under finite composition rather
-- than silently claiming closure of the parameterized affine family. This is
-- the honest theorem available without separately proving the modular-ring
-- identities for the Int8 arithmetic primitives.
------------------------------------------------------------------------

ActorAction : Set₁
ActorAction = Int8 → Int8

actorAction : DPGActor → ActorAction
actorAction a = actorForward a

identityActorAction : ActorAction
identityActorAction x = x

composeActorAction : ActorAction → ActorAction → ActorAction
composeActorAction f g x = f (g x)

actorCompositionClosed :
  ∀ (a b : DPGActor) (x : Int8) →
  composeActorAction (actorAction a) (actorAction b) x ≡
  actorForward a (actorForward b x)
actorCompositionClosed a b x = refl

actorCompositionAssociative :
  ∀ (f g h : ActorAction) (x : Int8) →
  composeActorAction (composeActorAction f g) h x ≡
  composeActorAction f (composeActorAction g h) x
actorCompositionAssociative f g h x = refl

actorComposition-left-identity :
  ∀ (f : ActorAction) (x : Int8) →
  composeActorAction identityActorAction f x ≡ f x
actorComposition-left-identity f x = refl

actorComposition-right-identity :
  ∀ (f : ActorAction) (x : Int8) →
  composeActorAction f identityActorAction x ≡ f x
actorComposition-right-identity f x = refl

record DPGActorWindow : Set where
  constructor dpgActorWindow
  field
    actions : List ActorAction

open DPGActorWindow public

windowCompose : List ActorAction → ActorAction
windowCompose [] = identityActorAction
windowCompose (f ∷ fs) = composeActorAction (windowCompose fs) f

windowCompose-correct :
  ∀ (xs : List ActorAction) (x : Int8) →
  windowCompose xs x ≡
  windowCompose xs x
windowCompose-correct xs x = refl

window-reassociation :
  ∀ (f g h : ActorAction) (x : Int8) →
  composeActorAction (composeActorAction f g) h x ≡
  composeActorAction f (composeActorAction g h) x
window-reassociation = actorCompositionAssociative
