{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.TheoremStrength where

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans; sym)
open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Exotic.ERL.Exploration.DyadicLaw using (DyadicLaw; lazyWalk; dyadicLadder; flatDyadic)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne
  ; there
  ; here
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
  baseLevel : MethodLevel
  representationLevel : MethodLevel

_≤method_ : MethodLevel → MethodLevel → Set
baseLevel ≤method baseLevel = ⊤
baseLevel ≤method representationLevel = ⊤
representationLevel ≤method representationLevel = ⊤
representationLevel ≤method baseLevel = ⊥

method-level-trans : ∀ {a b c} → a ≤method b → b ≤method c → a ≤method c
method-level-trans tt tt = tt

strict-method-representation : baseLevel ≤method representationLevel
strict-method-representation = tt

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

one-state-base : BaseEndogenous lazyWalk one-state-loop
one-state-base = baseEndogenous
  (record
    { lawNormalized = tt
    ; lawUnitSupport = tt
    ; representationForward = tt
    ; representationPullback = tt
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

strictBaseNotStrong : ¬ (BaseEndogenous lazyWalk one-state-loop →
  StrongEndogenous lazyWalk one-state-loop)
strictBaseNotStrong _ = no-two-point-retraction

data LawLevel : Set where
  lazyLevel : LawLevel
  ladderLevel : LawLevel
  flatLevel : LawLevel

_≤law_ : LawLevel → LawLevel → Set
lazyLevel ≤law lazyLevel = ⊤
lazyLevel ≤law ladderLevel = ⊤
lazyLevel ≤law flatLevel = ⊤
ladderLevel ≤law ladderLevel = ⊤
ladderLevel ≤law flatLevel = ⊤
flatLevel ≤law flatLevel = ⊤
_≤law_ _ _ = ⊥

law-level-trans : ∀ {a b c} → a ≤law b → b ≤law c → a ≤law c
law-level-trans tt tt = tt

strict-lazy-ladder : lazyLevel ≤law ladderLevel
strict-lazy-ladder = tt

strict-ladder-flat : ladderLevel ≤law flatLevel
strict-ladder-flat = tt

law-level : DyadicLaw → LawLevel
law-level lazyWalk = lazyLevel
law-level dyadicLadder = ladderLevel
law-level flatDyadic = flatLevel

data MethodTag : Set where
  mr15Tag : MethodTag
  openESTag : MethodTag
  noisyNetTag : MethodTag

method-level : MethodTag → MethodLevel
method-level mr15Tag = baseLevel
method-level openESTag = baseLevel
method-level noisyNetTag = representationLevel

_≤variant_ : MethodTag → DyadicLaw → MethodTag → DyadicLaw → Set
m₁ ≤variant l₁ m₂ l₂ =
  method-level m₁ ≤method method-level m₂ ×
  law-level l₁ ≤law law-level l₂

strongestDominates : ∀ (m : MethodTag) (l : DyadicLaw)
  → m ≤variant l noisyNetTag flatDyadic
strongestDominates mr15Tag l = tt , tt
strongestDominates openESTag l = tt , tt
strongestDominates noisyNetTag l = tt , tt
