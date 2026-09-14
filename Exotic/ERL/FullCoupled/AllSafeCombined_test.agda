{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AllSafeCombined_test where

open import Agda.Builtin.Equality using (_≡_; refl)
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
  )
open import Exotic.ERL.FullCoupled.MobiusGRU using
  ( Mobius
  )

mr15FlatReach :
  ∀ (s t : CanonicalState) → Reach (CoupledStep flatDyadic mr15GA) s t
mr15FlatReach s t = canonicalIrreducible mr15GA s t

openESFlatLoop :
  ∀ (s : CanonicalState) → SelfLoop (CoupledStep flatDyadic openES) s
openESFlatLoop s = canonicalSelfLoop openES s

noisyNetFlatPeriodOne :
  PeriodOne (CoupledStep flatDyadic noisyNetGRU)
noisyNetFlatPeriodOne = canonicalPeriodOne noisyNetGRU

representationClosed : ∀ x → canonicalRepresentationLaw x
representationClosed x = refl

projectionLiftClosed : ∀ x → noisyNetProjectionLift x
projectionLiftClosed x = noisyNetProjectionLift x

mobiusClosed : ∀ (a b c : Mobius) → canonicalMobiusAssoc a b c
mobiusClosed a b c = canonicalMobiusAssoc a b c
