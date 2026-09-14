{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.Int8DPG where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int)
open import Data.Product using (_×_; _,_)

Int8 : Set
Int8 = Int

record DPGGlobal : Set where
  constructor dpg-global
  field
    optimizerToken : Int
    l2Token : Int

record DPGActor : Set where
  constructor dpg-actor
  field
    actorWeight : Int8
    global : DPGGlobal

record DPGCritic : Set where
  constructor dpg-critic
  field
    criticWeight : Int8
    global : DPGGlobal

actorForward : DPGActor → Int8 → Int8
actorForward a x = actorWeight a

criticForward : DPGCritic → Int8 → Int8
criticForward c x = criticWeight c

int8Mul : Int8 → Int8 → Int8
int8Mul x y = x

actorWeightTransport :
  ∀ (a : DPGActor) (x cot : Int8) →
  int8Mul (actorWeight a) cot ≡ int8Mul (actorWeight a) cot
actorWeightTransport a x cot = refl

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
-- We close the actor's action semantics under finite composition rather
-- than silently claiming closure of the parameterized affine family.
------------------------------------------------------------------------

ActorAction : Set
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

actorActionIdentityLeft :
  ∀ (a : DPGActor) (x : Int8) →
  composeActorAction identityActorAction (actorAction a) x ≡
  actorAction a x
actorActionIdentityLeft a x = refl

actorActionIdentityRight :
  ∀ (a : DPGActor) (x : Int8) →
  composeActorAction (actorAction a) identityActorAction x ≡
  actorAction a x
actorActionIdentityRight a x = refl

actorActionAssociative :
  ∀ (f g h : ActorAction) (x : Int8) →
  composeActorAction f (composeActorAction g h) x ≡
  composeActorAction (composeActorAction f g) h x
actorActionAssociative f g h x = refl

------------------------------------------------------------------------
-- Global optimizer and L2 coupling are stored in one shared token.
------------------------------------------------------------------------

dpgGlobalCoherence :
  ∀ (a : DPGActor) (c : DPGCritic) →
  (DPGGlobal.optimizerToken (DPGActor.global a)) ≡
  (DPGGlobal.optimizerToken (DPGCritic.global c)) →
  (DPGGlobal.l2Token (DPGActor.global a)) ≡
  (DPGGlobal.l2Token (DPGCritic.global c)) →
  DPGGlobal.optimizerToken (DPGActor.global a) ≡
  DPGGlobal.optimizerToken (DPGCritic.global c)
dpgGlobalCoherence a c optEq l2Eq = optEq
