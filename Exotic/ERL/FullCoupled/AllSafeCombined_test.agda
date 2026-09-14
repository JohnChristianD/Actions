{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AllSafeCombined_test where

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
  ; lazy-normalized
  ; ladder-normalized
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
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGCoupled
  ; actorComponent
  ; criticComponent
  ; actorGlobalCoherence
  ; criticGlobalCoherence
  )

flatLazyNormalization : lazy-normalized
flatLazyNormalization = refl

ladderNormalization : ladder-normalized
ladderNormalization = refl

mr15FlatReach : ∀ s t → _
mr15FlatReach s t = canonicalIrreducible flatDyadic mr15GA s t

openESLazyLoop : ∀ s → _
openESLazyLoop s = canonicalSelfLoop lazyUnit openES s

noisyNetLadderPeriodOne : _
noisyNetLadderPeriodOne = canonicalPeriodOne dyadicLadder noisyNetGRU

representationClosed : ∀ x → canonicalRepresentationLaw x
representationClosed x = refl

projectionLiftClosed : ∀ x → noisyNetProjectionLift x
projectionLiftClosed x = noisyNetProjectionLift x

mobiusClosed : ∀ a b c → canonicalMobiusAssoc a b c
mobiusClosed a b c = canonicalMobiusAssoc a b c
