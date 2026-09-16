{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.JensenMinMaxSandwich where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)

record MidpointOrder : Set₁ where
  field
    Carrier : Set
    _≤_ : Carrier → Carrier → Set
    midpoint : Carrier → Carrier → Carrier
    le-refl : ∀ x → _≤_ x x
    le-trans : ∀ {x y z} → _≤_ x y → _≤_ y z → _≤_ x z
    midpoint-mono : ∀ {a b c d} → _≤_ a c → _≤_ b d →
      _≤_ (midpoint a b) (midpoint c d)

open MidpointOrder public

data DyadicTree (A : Set) : Nat → Set where
  leaf : A → DyadicTree A zero
  node : ∀ {n} → DyadicTree A n → DyadicTree A n → DyadicTree A (suc n)

dyadicMean : (M : MidpointOrder) → ∀ {n : Nat} →
  DyadicTree (Carrier M) n → Carrier M
dyadicMean M (leaf x) = x
dyadicMean M (node xs ys) = midpoint M (dyadicMean M xs) (dyadicMean M ys)

mapDyadicTree : ∀ {A B : Set} {n : Nat} →
  (A → B) → DyadicTree A n → DyadicTree B n
mapDyadicTree f (leaf x) = leaf (f x)
mapDyadicTree f (node xs ys) = node (mapDyadicTree f xs) (mapDyadicTree f ys)

record MidpointConvex {A B : MidpointOrder}
  (f : Carrier A → Carrier B) : Set₁ where
  field
    convexStep : ∀ x y →
      _≤_ B (f (midpoint A x y)) (midpoint B (f x) (f y))
open MidpointConvex public

record MidpointConcave {A B : MidpointOrder}
  (f : Carrier A → Carrier B) : Set₁ where
  field
    concaveStep : ∀ x y →
      _≤_ B (midpoint B (f x) (f y)) (f (midpoint A x y))
open MidpointConcave public

jensenDyadicConvex :
  ∀ {A B : MidpointOrder}
  {f : Carrier A → Carrier B} →
  MidpointConvex f →
  ∀ {n : Nat} (xs : DyadicTree (Carrier A) n) →
  _≤_ B (f (dyadicMean A xs))
    (dyadicMean B (mapDyadicTree f xs))
jensenDyadicConvex {f = f} C (leaf x) = le-refl B (f x)
jensenDyadicConvex C (node xs ys) =
  le-trans B
    (convexStep C (dyadicMean A xs) (dyadicMean A ys))
    (midpoint-mono B
      (jensenDyadicConvex C xs)
      (jensenDyadicConvex C ys))

jensenDyadicConcave :
  ∀ {A B : MidpointOrder}
  {f : Carrier A → Carrier B} →
  MidpointConcave f →
  ∀ {n : Nat} (xs : DyadicTree (Carrier A) n) →
  _≤_ B (dyadicMean B (mapDyadicTree f xs))
    (f (dyadicMean A xs))
jensenDyadicConcave {f = f} C (leaf x) = le-refl B (f x)
jensenDyadicConcave C (node xs ys) =
  le-trans B
    (midpoint-mono B
      (jensenDyadicConcave C xs)
      (jensenDyadicConcave C ys))
    (concaveStep C (dyadicMean A xs) (dyadicMean A ys))

record MidpointConvexConcave
  {X Y Z : MidpointOrder}
  (payoff : Carrier X → Carrier Y → Carrier Z) : Set₁ where
  field
    convexInLeft : ∀ x₁ x₂ y →
      _≤_ Z
        (payoff (midpoint X x₁ x₂) y)
        (midpoint Z (payoff x₁ y) (payoff x₂ y))
    concaveInRight : ∀ x y₁ y₂ →
      _≤_ Z
        (midpoint Z (payoff x y₁) (payoff x y₂))
        (payoff x (midpoint Y y₁ y₂))
open MidpointConvexConcave public

convexConcaveJensenSandwich :
  ∀ {X Y Z : MidpointOrder}
  {payoff : Carrier X → Carrier Y → Carrier Z}
  → MidpointConvexConcave payoff
  → ∀ {n m : Nat}
    (xs : DyadicTree (Carrier X) n)
    (ys : DyadicTree (Carrier Y) m)
    →
    (_≤_ Z
      (dyadicMean Z
        (mapDyadicTree
          (λ y → payoff (dyadicMean X xs) y)
          ys))
      (payoff (dyadicMean X xs) (dyadicMean Y ys))) ×
    (_≤_ Z
      (payoff (dyadicMean X xs) (dyadicMean Y ys))
      (dyadicMean Z
        (mapDyadicTree
          (λ x → payoff x (dyadicMean Y ys))
          xs)))
convexConcaveJensenSandwich C xs ys =
  jensenDyadicConcave
    (record
      { concaveStep = λ y₁ y₂ →
          concaveInRight C (dyadicMean X xs) y₁ y₂
      })
    ys
  ,
  jensenDyadicConvex
    (record
      { convexStep = λ x₁ x₂ →
          convexInLeft C x₁ x₂ (dyadicMean Y ys)
      })
    xs

jensenMidpointIdentity : ∀ {M : MidpointOrder} {x : Carrier M} →
  dyadicMean M (leaf x) ≡ x
jensenMidpointIdentity = refl
