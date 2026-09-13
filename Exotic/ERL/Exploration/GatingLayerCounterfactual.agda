{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.GatingLayerCounterfactual where

open import Agda.Builtin.Equality using (_≡_; refl; trans)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; here
  ; there
  ; Irreducible
  )

record GatingFactorization (Full Gate : Set) where
  field
    project : Full → Gate
    lift : Gate → Full

    project-lift : ∀ g → project (lift g) ≡ g

    GateStep : Gate → Gate → Set
    FullStep : Full → Full → Set

    lift-step : ∀ {g h} → GateStep g h → FullStep (lift g) (lift h)

open GatingFactorization public

gate-reach-lifts : ∀ {Full Gate : Set}
  (F : GatingFactorization Full Gate)
  {g h : Gate}
  → Reach (GateStep F) g h
  → Reach (FullStep F) (lift F g) (lift F h)
gate-reach-lifts F here = here
gate-reach-lifts F (there step rest) =
  there (lift-step F step) (gate-reach-lifts F rest)

project-after-lift : ∀ {Full Gate : Set}
  (F : GatingFactorization Full Gate)
  → ∀ g → project F (lift F g) ≡ g
project-after-lift F = project-lift F

first-coordinate-preserved : ∀ {Learner Gate : Set}
  {step : (Learner × Gate) → (Learner × Gate) → Set}
  → (∀ {l l' : Learner} {g g' : Gate}
      → step (l , g) (l' , g')
      → l ≡ l')
  → ∀ {l l' : Learner} {g g' : Gate}
      → Reach step (l , g) (l' , g')
      → l ≡ l'
first-coordinate-preserved inv here = refl
first-coordinate-preserved inv (there step rest) =
  trans (inv step) (first-coordinate-preserved inv rest)

gating-only-not-irreducible : ∀ {Learner Gate : Set}
  {step : (Learner × Gate) → (Learner × Gate) → Set}
  → (∀ {l l' : Learner} {g g' : Gate}
      → step (l , g) (l' , g')
      → l ≡ l')
  → (l₀ l₁ : Learner)
  → (g₀ : Gate)
  → (l₀ ≡ l₁ → ⊥)
  → ¬ Irreducible step
gating-only-not-irreducible inv l₀ l₁ g₀ neq irr =
  neq (first-coordinate-preserved inv (irr (l₀ , g₀) (l₁ , g₀)))
