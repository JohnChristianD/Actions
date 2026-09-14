{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; Method
  ; flatDyadic
  ; noisyNetGRU
  ; law-has-zero
  ; law-has-unit-generator
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; SelfLoop
  ; PeriodOne
  )
open import Exotic.ERL.FullCoupled.DyadicMethodLawCoupling using
  ( CanonicalState
  ; CoupledStep
  ; coupledIrreducible
  ; coupledSelfLoop
  ; coupledPeriodOne
  )
open import Exotic.ERL.FullCoupled.MobiusGRU using
  ( Mobius
  ; compose
  ; compose-assoc
  ; compose-identity-left
  ; compose-identity-right
  )
open import Exotic.ERL.FullCoupled.DyadicRepresentation using
  ( representationCompose
  )
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGActor
  ; actorAction
  ; ActorAction
  ; composeActorAction
  ; actorCompositionClosed
  ; actorCompositionAssociative
  ; actorComposition-left-identity
  ; actorComposition-right-identity
  )

canonicalLaw0 : Law
canonicalLaw0 = flatDyadic

canonicalMethod0 : Method
canonicalMethod0 = noisyNetGRU

canonicalState : Set
canonicalState = CanonicalState

canonicalIrreducible :
  ∀ (m : Method) →
  ∀ s t → Reach (CoupledStep flatDyadic m) s t
canonicalIrreducible = coupledIrreducible

canonicalSelfLoop :
  ∀ (m : Method) →
  SelfLoop (CoupledStep flatDyadic m)
canonicalSelfLoop = coupledSelfLoop

canonicalPeriodOne :
  ∀ (m : Method) →
  PeriodOne (CoupledStep flatDyadic m)
canonicalPeriodOne = coupledPeriodOne

canonicalFlatZero = law-has-zero flatDyadic
canonicalFlatGenerator = law-has-unit-generator flatDyadic

canonicalRepresentationLaw :
  ∀ x → representationCompose x ≡ representationCompose x
canonicalRepresentationLaw x = refl

canonicalMobiusAssoc :
  ∀ (a b c : Mobius) →
  compose (compose a b) c ≡ compose a (compose b c)
canonicalMobiusAssoc = compose-assoc

canonicalMobiusLeft : ∀ a → compose (record { run = λ x → x }) a ≡ a
canonicalMobiusLeft a = compose-identity-left a

canonicalMobiusRight : ∀ a → compose a (record { run = λ x → x }) ≡ a
canonicalMobiusRight a = compose-identity-right a

canonicalFiniteIdentity :
  ∀ (x : Int8) → x ≡ x
canonicalFiniteIdentity x = refl

------------------------------------------------------------------------
-- DPG actor action closure is part of the canonical composition surface.
------------------------------------------------------------------------

canonicalActorClosure :
  ∀ (a b : DPGActor) (x : Int8) →
  composeActorAction (actorAction a) (actorAction b) x ≡
  actorAction a (actorAction b x)
canonicalActorClosure = actorCompositionClosed

canonicalActorAssoc :
  ∀ (f g h : ActorAction) (x : Int8) →
  composeActorAction (composeActorAction f g) h x ≡
  composeActorAction f (composeActorAction g h) x
canonicalActorAssoc = actorCompositionAssociative

canonicalActorLeftId :
  ∀ (f : ActorAction) (x : Int8) →
  composeActorAction (λ y → y) f x ≡ f x
canonicalActorLeftId = actorComposition-left-identity

canonicalActorRightId :
  ∀ (f : ActorAction) (x : Int8) →
  composeActorAction f (λ y → y) x ≡ f x
canonicalActorRightId = actorComposition-right-identity
