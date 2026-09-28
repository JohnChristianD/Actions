{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Unconditional stationary price-law seam.
--
-- This module removes the external price-update-function parameter from
-- the unconditional core by choosing the canonical zero-step operator.
-- It proves stationarity by reflexivity. It does not claim that this
-- identity operator is a classical excess-demand adjustment process.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.CanonicalAggregatePriceLaw where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Exotic.ERL.FullCoupled.TheoremsMonolith

canonicalStationaryPriceUpdate :
  {Price : Set} →
  Price →
  Price
canonicalStationaryPriceUpdate p = p

canonicalStationaryPriceLaw :
  {Price : Set} →
  ∀ p →
  canonicalStationaryPriceUpdate p ≡ p
canonicalStationaryPriceLaw p = refl

record UnconditionalEGraphEconomicStationaryPriceComposition
  (Expression State Price : Set)
  (R :
    EGraphSemanticInterpretation
      Expression
      State)
  (e f : Expression) : Set₁ where
  constructor unconditionalEGraphEconomicStationaryPriceComposition
  field
    semanticPath :
      EGraphSemanticPath R e f
    stationaryPriceLaw :
      ∀ p →
      canonicalStationaryPriceUpdate p ≡ p

unconditionalEGraphEconomicStationaryPriceClosure :
  ∀ {Expression State Price : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  (W :
    UnconditionalEGraphEconomicStationaryPriceComposition
      Expression
      State
      Price
      R
      e
      f) →
  EGraphSemanticPath R e f ×
  (∀ p →
    canonicalStationaryPriceUpdate p ≡ p)
unconditionalEGraphEconomicStationaryPriceClosure W =
  UnconditionalEGraphEconomicStationaryPriceComposition.semanticPath W
  , UnconditionalEGraphEconomicStationaryPriceComposition.stationaryPriceLaw W

unconditionalEGraphEconomicStationaryPriceComposition-from-path :
  ∀ {Expression State Price : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  (path : EGraphSemanticPath R e f) →
  UnconditionalEGraphEconomicStationaryPriceComposition
    Expression
    State
    Price
    R
    e
    f
unconditionalEGraphEconomicStationaryPriceComposition-from-path path =
  unconditionalEGraphEconomicStationaryPriceComposition
    path
    canonicalStationaryPriceLaw

------------------------------------------------------------------------
-- The unconditional result is intentionally a stationarity theorem.
-- A non-identity price-adjustment law requires an explicit economic
-- structure relating excess demand to price motion; no such structure is
-- invented here.
------------------------------------------------------------------------
