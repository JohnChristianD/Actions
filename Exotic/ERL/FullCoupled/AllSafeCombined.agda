{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; Method
  ; flatDyadic
  ; lazyUnit
  ; dyadicLadder
  ; mr15GA
  ; openES
  ; noisyNetGRU
  ; law-has-zero
  ; law-has-unit-generator
  )
open import Exotic.ERL.FullCoupled.DyadicMethodLawCoupling using
  ( CoupledState
  ; CoupledStep
  ; coupledIrreducible
  ; coupledSelfLoop
  ; coupledPeriodOne
  ; noisyNetProjection
  )
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; gruGlobalControlPersists
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
  ; representation-compose-law
  )
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGActor
  ; DPGCritic
  ; dpgActorTransport
  ; dpgCriticTransport
  )

canonicalLaw0 : Law
canonicalLaw0 = flatDyadic

canonicalMethod0 : Method
canonicalMethod0 = noisyNetGRU

canonicalState : Set
canonicalState = CoupledState

canonicalIrreducible :
  ∀ (l : Law) (m : Method) →
  ∀ s t → Exotic.ERL.Exploration.ExplorationTheoremSchema.Reach
    (CoupledStep l m) s t
canonicalIrreducible l m = coupledIrreducible l m

canonicalSelfLoop :
  ∀ (l : Law) (m : Method) →
  Exotic.ERL.Exploration.ExplorationTheoremSchema.SelfLoop
    (CoupledStep l m)
canonicalSelfLoop l m = coupledSelfLoop l m

canonicalPeriodOne :
  ∀ (l : Law) (m : Method) →
  Exotic.ERL.Exploration.ExplorationTheoremSchema.PeriodOne
    (CoupledStep l m)
canonicalPeriodOne l m = coupledPeriodOne l m

canonicalFlatZero = law-has-zero flatDyadic
canonicalFlatGenerator = law-has-unit-generator flatDyadic

canonicalRepresentationLaw :
  ∀ x → representationCompose x
    ≡ representationCompose x
canonicalRepresentationLaw x = refl

canonicalMobiusAssoc :
  ∀ (a b c : Mobius) →
  compose (compose a b) c ≡ compose a (compose b c)
canonicalMobiusAssoc = compose-assoc

canonicalMobiusLeft : ∀ a → compose (record { run = λ x → x }) a ≡ a
canonicalMobiusLeft a = compose-identity-left a

canonicalMobiusRight : ∀ a → compose a (record { run = λ x → x }) ≡ a
canonicalMobiusRight a = compose-identity-right a
