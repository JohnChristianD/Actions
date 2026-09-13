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

-- The full theorem object carries the finite law, the actual explorer,
-- and the representation-layer CHAD composition. PeriodOne is derived only
-- after those components are packaged together.
record FullAlgebraicCoupling {S : Set}
    (law : DyadicLaw) (_—→_ : S → S → Set) : Set₂ where
  constructor fullAlgebraicCoupling
  field
    lawNormalized : law-normalized law
    lawUnitSupport : law-unit-support law
    representationForward : softsignGatedForwardLaw
    representationPullback : softsignGatedPullbackLaw
    irreducible : Irreducible _—→_
    selfLoop : SelfLoop _—→_
    periodOne : PeriodOne _—→_

composeFull : ∀ {S : Set} (law : DyadicLaw) {_—→_ : S → S → Set}
  → law-normalized law
  → law-unit-support law
  → softsignGatedForwardLaw
  → softsignGatedPullbackLaw
  → Irreducible _—→_
  → SelfLoop _—→_
  → FullAlgebraicCoupling law _—→
composeFull law normalized support representationForward representationPullback r loop =
  fullAlgebraicCoupling
    normalized
    support
    representationForward
    representationPullback
    r
    loop
    (periodOne-from-components r loop)
