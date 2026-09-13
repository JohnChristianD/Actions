{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FullAlgebraicCoupling where

open import Exotic.ERL.Exploration.DyadicLaw using
  ( DyadicLaw
  ; law-normalized
  ; law-unit-support
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne-from-components
  )
open import Exotic.efficient_chad.SoftsignGatedComposition using
  ( softsignGatedForwardLaw
  ; softsignGatedPullbackLaw
  )
open import Exotic.ERL.FullCoupled.SoftsignGatedRepresentation using
  ( SoftsignGatedStep
  ; softsignGatedPeriodOne
  )

record FullAlgebraicCoupling {S : Set}
    (law : DyadicLaw) (_—→_ : S → S → Set) : Set₂ where
  constructor fullAlgebraicCoupling
  field
    lawNormalized : law-normalized law
    lawUnitSupport : law-unit-support law
    representationForward : softsignGatedForwardLaw
    representationPullback : softsignGatedPullbackLaw
    canonicalRepresentation : PeriodOne SoftsignGatedStep
    irreducible : Irreducible _—→_
    selfLoop : SelfLoop _—→_
    periodOne : PeriodOne _—→_

composeFull : ∀ {S : Set} (law : DyadicLaw) {_—→_ : S → S → Set}
  → law-normalized law
  → law-unit-support law
  → softsignGatedForwardLaw
  → softsignGatedPullbackLaw
  → PeriodOne SoftsignGatedStep
  → Irreducible _—→_
  → SelfLoop _—→_
  → FullAlgebraicCoupling law _—→
composeFull law normalized support representationForward representationPullback canonicalRepresentation r loop =
  fullAlgebraicCoupling
    normalized
    support
    representationForward
    representationPullback
    canonicalRepresentation
    r
    loop
    (periodOne-from-components r loop)
