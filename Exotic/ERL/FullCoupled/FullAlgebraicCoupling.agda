{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FullAlgebraicCoupling where

open import Exotic.ERL.Exploration.DyadicLaw using
  ( DyadicLaw
  ; law-normalized
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne-from-components
  )

record FullAlgebraicCoupling {S : Set}
    (law : DyadicLaw) (_—→_ : S → S → Set) : Set where
  constructor fullAlgebraicCoupling
  field
    lawNormalized : law-normalized law
    irreducible : Irreducible _—→_
    selfLoop : SelfLoop _—→_
    periodOne : PeriodOne _—→_

composeFull : ∀ {S : Set} (law : DyadicLaw) {_—→_ : S → S → Set}
  → law-normalized law
  → Irreducible _—→_
  → SelfLoop _—→_
  → FullAlgebraicCoupling law _—→_
composeFull law normalized r loop =
  fullAlgebraicCoupling
    normalized
    r
    loop
    (periodOne-from-components r loop)
