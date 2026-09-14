{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FullAlgebraicCoupling where

open import Exotic.ERL.Exploration.DyadicLaw using
  ( DyadicLaw
  ; law-normalized
  ; law-unit-support
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Aperiodic
  ; Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne-from-components
  )
open import Exotic.ERL.FullCoupled.GRUComposition using
  ( GRUComposition )

record FullAlgebraicCoupling {S : Set}
    (law : DyadicLaw) (_—→_ : S → S → Set) : Set₂ where
  constructor fullAlgebraicCoupling
  field
    lawNormalized : law-normalized law
    lawUnitSupport : law-unit-support law
    architecture : GRUComposition
    irreducible : Irreducible _—→_
    selfLoop : SelfLoop _—→_
    periodOne : PeriodOne _—→_
    aperiodic : Aperiodic _—→_

composeFull : ∀ {S : Set} (law : DyadicLaw) {_—→_ : S → S → Set}
  → law-normalized law
  → law-unit-support law
  → GRUComposition
  → Irreducible _—→_
  → SelfLoop _—→_
  → FullAlgebraicCoupling law _—→
composeFull law normalized support architecture r loop =
  fullAlgebraicCoupling
    normalized
    support
    architecture
    r
    loop
    (periodOne-from-components r loop)
    (periodOne-from-components r loop)
