{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.TheoremStrengthV2 where

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
open import Exotic.efficient_chad.SoftsignGatedComposition using
  ( softsignGatedForwardLaw-proof
  ; softsignGatedPullbackLaw-proof
  )
open import Exotic.ERL.Exploration.DyadicLaw using
  ( lazyWalkNormalized
  ; lazyWalkUnitSupport
  )
open import Exotic.ERL.FullCoupled.FullAlgebraicCoupling using (FullAlgebraicCoupling)
open import Exotic.ERL.FullCoupled.SoftsignGatedRepresentation using (RepresentationFactor)

record BaseEndogenous {S : Set} (law : DyadicLaw) (stepS : S → S → Set) : Set₂ where
  constructor baseEndogenous
  field
    fullTheorem : FullAlgebraicCoupling law stepS

record StrongEndogenous {S R : Set}
    (law : DyadicLaw)
    (stepS : S → S → Set)
    (stepR : R → R → Set) : Set₂ where
  constructor strongEndogenous
  field
    fullTheorem : FullAlgebraicCoupling law stepS
    representationFactor : RepresentationFactor stepS stepR

forgetRepresentation : ∀ {S R : Set} {law : DyadicLaw}
    {stepS : S → S → Set} {stepR : R → R → Set}
  → StrongEndogenous {S = S} {R = R} law stepS stepR
  → BaseEndogenous law stepS
forgetRepresentation (strongEndogenous f _) = baseEndogenous f

data MethodLevel : Set where
  baseLevel : MethodLevel
  representationLevel : MethodLevel

_≤method_ : MethodLevel → MethodLevel → Set
baseLevel ≤method baseLevel = ⊤
baseLevel ≤method representationLevel = ⊤
representationLevel ≤method representationLevel = ⊤
representationLevel ≤method baseLevel = ⊥

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
    { lawNormalized = lazyWalkNormalized
    ; lawUnitSupport = lazyWalkUnitSupport
    ; representationForward = softsignGatedForwardLaw-proof
    ; representationPullback = softsignGatedPullbackLaw-proof
    ; irreducible = one-state-irreducible
    ; selfLoop = one-state-selfLoop
    ; periodOne = one-state-periodOne
    })

one-unique : ∀ x y → x ≡ y
one-unique oneState oneState = refl

false≠true : ¬ (false ≡ true)
false≠true ()

bool-loop : Bool → Bool → Set
bool-loop _ _ = ⊤

no-two-point-factor : ¬ RepresentationFactor one-state-loop bool-loop
no-two-point-factor (representationFactor p l r _ _) =
  false≠true (trans (r false)
    (trans (cong p (one-unique (l false) (l true)))
      (sym (r true))))

strictBaseNotStrong : ¬ (BaseEndogenous lazyWalk one-state-loop →
  StrongEndogenous {S = OneState} {R = Bool} lazyWalk one-state-loop bool-loop)
strictBaseNotStrong _ = no-two-point-factor

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
