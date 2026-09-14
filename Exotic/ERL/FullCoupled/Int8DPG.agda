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
-- We close the actor's action semantics under finite composition rather
-- than silently claiming closure of the parameterized affine family.
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
  windowCompose xs x ≡ windowCompose xs x
windowCompose-correct xs x = refl

window-reassociation :
  ∀ (f g h : ActorAction) (x : Int8) →
  composeActorAction (composeActorAction f g) h x ≡
  composeActorAction f (composeActorAction g h) x
window-reassociation = actorCompositionAssociative

------------------------------------------------------------------------
-- One representation is shared by actor and critic.
------------------------------------------------------------------------

SharedRepresentation : Set₁
SharedRepresentation = Int8 → Int8

sharedRepresentationIdentity : SharedRepresentation
sharedRepresentationIdentity x = x

composeSharedRepresentation :
  SharedRepresentation → SharedRepresentation → SharedRepresentation
composeSharedRepresentation f g x = f (g x)

actorAfterShared :
  DPGActor → SharedRepresentation → ActorAction
actorAfterShared a r x = actorForward a (r x)

criticAfterShared :
  DPGCritic → SharedRepresentation → ActorAction
criticAfterShared c r x = criticForward c (r x)

sharedRepresentation-factor-actor :
  ∀ (a : DPGActor) (r : SharedRepresentation) (x : Int8) →
  actorAfterShared a r x ≡ actorForward a (r x)
sharedRepresentation-factor-actor a r x = refl

sharedRepresentation-factor-critic :
  ∀ (c : DPGCritic) (r : SharedRepresentation) (x : Int8) →
  criticAfterShared c r x ≡ criticForward c (r x)
sharedRepresentation-factor-critic c r x = refl

sharedRepresentation-once :
  ∀ (a : DPGActor) (c : DPGCritic)
    (r : SharedRepresentation) (x : Int8) →
  (actorAfterShared a r x , criticAfterShared c r x)
  ≡
  (actorForward a (r x) , criticForward c (r x))
sharedRepresentation-once a c r x = refl

sharedRepresentation-reassociation :
  ∀ (a : DPGActor) (r s : SharedRepresentation) (x : Int8) →
  actorAfterShared a (composeSharedRepresentation r s) x
  ≡ actorForward a (r (s x))
sharedRepresentation-reassociation a r s x = refl

sharedRepresentation-critic-reassociation :
  ∀ (c : DPGCritic) (r s : SharedRepresentation) (x : Int8) →
  criticAfterShared c (composeSharedRepresentation r s) x
  ≡ criticForward c (r (s x))
sharedRepresentation-critic-reassociation c r s x = refl

record SharedDPGBand : Set₁ where
  constructor sharedDPGBand
  field
    representation : SharedRepresentation
    actor : DPGActor
    critic : DPGCritic

open SharedDPGBand public

sharedActor : SharedDPGBand → ActorAction
sharedActor b = actorAfterShared (actor b) (representation b)

sharedCritic : SharedDPGBand → ActorAction
sharedCritic b = criticAfterShared (critic b) (representation b)

sharedBand-law :
  ∀ (b : SharedDPGBand) (x : Int8) →
  (sharedActor b x , sharedCritic b x)
  ≡
  ( actorForward (actor b) (representation b x)
  , criticForward (critic b) (representation b x))
sharedBand-law b x = refl
