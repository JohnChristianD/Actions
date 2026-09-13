{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FullAlgebraicCoupling where

open import Exotic.ERL.Exploration.DyadicLaw using
  ( DyadicLaw
  ; law-normalized
  ; law-unit-support
  ; law-universal-support
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

-- The full theorem object carries the finite law, actual explorer transition,
-- representation-layer CHAD composition, and complete support. PeriodOne is
-- derived only after all coupled obligations are packaged together.
record FullAlgebraicCoupling {S : Set}
    (law : DyadicLaw) (_—→_ : S → S → Set) : Set₂ where
  constructor fullAlgebraicCoupling
  field
    lawNormalized : law-normalized law
    lawUnitSupport : law-unit-support law
    lawUniversalSupport : law-universal-support law
    representationForward : softsignGatedForwardLaw
    representationPullback : softsignGatedPullbackLaw
    irreducible : Irreducible _—→_
    selfLoop : SelfLoop _—→_
    periodOne : PeriodOne _—→_

composeFull : ∀ {S : Set} (law : DyadicLaw) {_—→_ : S → S → Set}
  → law-normalized law
  → law-unit-support law
  → law-universal-support law
  → softsignGatedForwardLaw
  → softsignGatedPullbackLaw
  → Irreducible _—→_
  → SelfLoop _—→_
  → FullAlgebraicCoupling law _—→
composeFull law normalized support universalSupport representationForward representationPullback r loop =
  fullAlgebraicCoupling
    normalized
    support
    universalSupport
    representationForward
    representationPullback
    r
    loop
    (periodOne-from-components r loop)
