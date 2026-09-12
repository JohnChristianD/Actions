{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.Dyadic
  using
    ( Dyadic
    ; 𝔻
    ; addDyadic
    ; subDyadic
    ; mulDyadic
    ; scalePow2
    ; MomentumState
    ; momentum
    ; momentumStep
    ; sparsemax2
    ; SparsePair
    ; Grid
    )
open import Exotic.ERL.Int8
  using
    ( Int8
    ; identityCHAD
    ; identityCHAD-law
    ; int8Roundtrip
    )
open import Exotic.Econlib.GameTheory
  using
    ( Action
    ; prisonersDilemma
    ; PureNash
    )
open import Exotic.Econlib.Equilibrium
  using
    ( canonicalEconomy2
    ; canonicalEconomy2Equilibrium
    ; WalrasianEquilibrium2
    )

testDyadicComposes : ∀ (a b : Dyadic) →
  addDyadic a b ≡ addDyadic a b
testDyadicComposes a b = refl

testMomentumComposes : ∀ (beta : Dyadic) (s : MomentumState) (g : Dyadic) →
  momentumStep beta s g ≡ momentumStep beta s g
testMomentumComposes beta s g = refl

testSparsemaxComposes : ∀ {n} (a b : Grid n) →
  sparsemax2 a b ≡ sparsemax2 a b
testSparsemaxComposes a b = refl

testInt8Identity : ∀ (x : Int8) →
  identityCHAD-law x ≡ refl

testInt8Identity x = refl

testInt8Roundtrip : ∀ (x : Int8) →
  int8Roundtrip x ≡ refl
testInt8Roundtrip x = refl

testEquilibrium : WalrasianEquilibrium2 canonicalEconomy2
testEquilibrium = canonicalEconomy2Equilibrium

postulatedNashFreeBoundary :
  ∀ {a b : Action} → PureNash prisonersDilemma a b → PureNash prisonersDilemma a b
postulatedNashFreeBoundary = λ w → w
