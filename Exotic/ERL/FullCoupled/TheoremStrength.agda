{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.TheoremStrength where

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans; sym)
open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Exotic.ERL.Exploration.DyadicLaw using (DyadicLaw; flatDyadic)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne
  ; there
  ; here
  )
open import Exotic.efficient_chad.SoftsignGatedComposition using
  ( softsignGatedForwardLaw-proof
  ; softsignGatedPullbackLaw-proof
  )
open import Exotic.ERL.Exploration.DyadicLaw using
  ( flatDyadicNormalized
  ; flatDyadicUnitSupport
  )
open import Exotic.ERL.FullCoupled.FullAlgebraicCoupling using (FullAlgebraicCoupling)
open import Exotic.ERL.FullCoupled.SoftsignGatedRepresentation using (RepresentationRetraction)

record BaseEndogenous {S : Set} (law : DyadicLaw) (_—→_ : S → S → Set) : Set₂ where
  constructor baseEndogenous
  field
    fullTheorem : FullAlgebraicCoupling law _—→_

record StrongEndogenous {S R : Set} (law : DyadicLaw) (_—→_ : S → S → Set) : Set₂ where
  constructor strongEndogenous
  field
    fullTheorem : FullAlgebraicCoupling law _—→_
    representationFactor : RepresentationRetraction {S = S} {R = R}

forgetRepresentation : ∀ {S R : Set} {law : DyadicLaw} {_—→_ : S → S → Set}
  → StrongEndogenous law _—→_
  → BaseEndogenous law _—→_
forgetRepresentation (strongEndogenous f _) = baseEndogenous f

data MethodLevel : Set where
  quotientLevel : MethodLevel
  representationLevel : MethodLevel
  coupledLevel : MethodLevel

_≤method_ : MethodLevel → MethodLevel → Set
quotientLevel ≤method quotientLevel = ⊤
quotientLevel ≤method representationLevel = ⊤
quotientLevel ≤method coupledLevel = ⊤
representationLevel ≤method representationLevel = ⊤
representationLevel ≤method coupledLevel = ⊤
coupledLevel ≤method coupledLevel = ⊤
_≤method_ _ _ = ⊥

method-level-trans : ∀ {a b c} → a ≤method b → b ≤method c → a ≤method c
method-level-trans tt tt = tt

strict-quotient-representation : quotientLevel ≤method representationLevel
strict-quotient-representation = tt

strict-representation-coupled : representationLevel ≤method coupledLevel
strict-representation-coupled = tt

data OneState : Set where
  oneState : OneState

one-state-loop : OneState → OneState → Set
one-state-loop oneState oneState = ⊤

one-state-irreducible : Irreducible one-state-loop
one-state-irreducible oneState oneState = there tt here

one-state-selfLoop : SelfLoop one-state-loop
one-state-selfLoop oneState = tt

one-state-periodOne : PeriodOne one-state-loop
one-state-periodOne = periodOne one-state-irreducible one-state-selfLoop

one-state-base : BaseEndogenous flatDyadic one-state-loop
one-state-base = baseEndogenous
  (record
    { lawNormalized = flatDyadicNormalized
    ; lawUnitSupport = flatDyadicUnitSupport
    ; representationForward = softsignGatedForwardLaw-proof
    ; representationPullback = softsignGatedPullbackLaw-proof
    ; canonicalRepresentation = one-state-periodOne
    ; irreducible = one-state-irreducible
    ; selfLoop = one-state-selfLoop
    ; periodOne = one-state-periodOne
    })

one-unique : ∀ x y → x ≡ y
one-unique oneState oneState = refl

false≠true : ¬ (false ≡ true)
false≠true ()

no-two-point-retraction : ¬ RepresentationRetraction {S = OneState} {R = Bool}
no-two-point-retraction (representationRetraction p l r) =
  false≠true (trans (r false)
    (trans (cong p (one-unique (l false) (l true)))
      (sym (r true))))

strictBaseNotStrong : ¬ (BaseEndogenous flatDyadic one-state-loop →
  StrongEndogenous flatDyadic one-state-loop)
strictBaseNotStrong _ = no-two-point-retraction
