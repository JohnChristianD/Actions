{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteAperiodicity where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ)

infixr 5 _∷ᵖ_

data Path {S : Set} (edge : S → S → Set) : ℕ → S → S → Set where
  []ᵖ : ∀ {x} → Path edge zero x x
  _∷ᵖ_ : ∀ {n x y z} →
    edge x y →
    Path edge n y z →
    Path edge (suc n) x z

infixr 5 _++ᵖ_

_++ᵖ_ : ∀ {S : Set} {edge : S → S → Set}
  {m n : ℕ} {x y z : S} →
  Path edge m x y →
  Path edge n y z →
  Path edge (n + m) x z
[]ᵖ ++ᵖ q = q
(e ∷ᵖ p) ++ᵖ q = e ∷ᵖ (p ++ᵖ q)

ExactReach : ∀ {S : Set} (edge : S → S → Set) →
  S → S → Set
ExactReach edge x y =
  Σ ℕ (λ n → Path edge n x y)

exactHere : ∀ {S : Set} {edge : S → S → Set} {x : S} →
  ExactReach edge x x
exactHere = zero , []ᵖ

exactTrans : ∀ {S : Set} {edge : S → S → Set}
  {x y z : S} →
  ExactReach edge x y →
  ExactReach edge y z →
  ExactReach edge x z
exactTrans (m , p) (n , q) = (n + m) , (p ++ᵖ q)

record SelfLoop {S : Set} (edge : S → S → Set) : Set where
  constructor selfLoop
  field
    hub : S
    loop : edge hub hub

record Irreducible {S : Set} (edge : S → S → Set) : Set₁ where
  constructor irreducible
  field
    reach : ∀ (x y : S) → ExactReach edge x y

record ConsecutiveReturn {S : Set} (edge : S → S → Set) (x : S) : Set where
  constructor consecutiveReturn
  field
    n : ℕ
    return₁ : Path edge (suc n) x x
    return₂ : Path edge (suc (suc n)) x x

record AperiodicViaConsecutiveReturns {S : Set}
  (edge : S → S → Set) : Set₁ where
  constructor aperiodic
  field
    at : ∀ x → ConsecutiveReturn edge x

hubAperiodicity : ∀ {S : Set} {edge : S → S → Set} →
  Irreducible edge →
  SelfLoop edge →
  AperiodicViaConsecutiveReturns edge
hubAperiodicity ir loop =
  aperiodic λ x →
    let
      h = SelfLoop.hub loop
      l = SelfLoop.loop loop
      m , left = Irreducible.reach ir x h
      n , right = Irreducible.reach ir h x
    in
    consecutiveReturn
      (n + m)
      ((left ++ᵖ (l ∷ᵖ []ᵖ)) ++ᵖ right)
      ((left ++ᵖ (l ∷ᵖ (l ∷ᵖ []ᵖ))) ++ᵖ right)

oneLoopIsAperiodicAtHub : ∀ {S : Set} {edge : S → S → Set}
  {h : S} →
  (l : edge h h) →
  ConsecutiveReturn edge h
oneLoopIsAperiodicAtHub l =
  consecutiveReturn
    zero
    (l ∷ᵖ []ᵖ)
    (l ∷ᵖ (l ∷ᵖ []ᵖ))
