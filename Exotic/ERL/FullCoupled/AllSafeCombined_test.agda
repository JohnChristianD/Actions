{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AllSafeCombined_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.Exploration.DyadicLaws using
  ( flatDyadic
  ; mr15GA
  ; openES
  ; noisyNetGRU
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; SelfLoop
  ; PeriodOne
  )
open import Exotic.ERL.FullCoupled.DyadicMethodLawCoupling using
  ( CanonicalState
  ; CoupledStep
  ; RecurrentProjection
  )
open import Exotic.ERL.FullCoupled.AllSafeCombined using
  ( canonicalIrreducible
  ; canonicalSelfLoop
  ; canonicalPeriodOne
  ; canonicalRepresentationLaw
  ; canonicalMobiusAssoc
  )
open import Exotic.ERL.FullCoupled.NoisyNetCoupled using
  ( noisyNetProjectionLift
  ; noisyNetRecurrentProjection
  )
open import Exotic.ERL.FullCoupled.DyadicRepresentation using
  ( representationCompose
  )
open import Exotic.ERL.FullCoupled.MobiusGRU using
  ( Mobius
  ; compose
  )

mr15FlatReach :
  ∀ (s t : CanonicalState) → Reach (CoupledStep flatDyadic mr15GA) s t
mr15FlatReach s t = canonicalIrreducible mr15GA s t

openESFlatLoop :
  SelfLoop (CoupledStep flatDyadic openES)
openESFlatLoop = canonicalSelfLoop openES

noisyNetFlatPeriodOne :
  PeriodOne (CoupledStep flatDyadic noisyNetGRU)
noisyNetFlatPeriodOne = canonicalPeriodOne noisyNetGRU

representationClosed :
  ∀ x → representationCompose x ≡ representationCompose x
representationClosed x = canonicalRepresentationLaw x

projectionLiftClosed :
  ∀ x →
  RecurrentProjection.project noisyNetRecurrentProjection
    (RecurrentProjection.lift noisyNetRecurrentProjection x) ≡ x
projectionLiftClosed x = noisyNetProjectionLift x

mobiusClosed :
  ∀ (a b c : Mobius) →
  compose (compose a b) c ≡ compose a (compose b c)
mobiusClosed a b c = canonicalMobiusAssoc a b c
