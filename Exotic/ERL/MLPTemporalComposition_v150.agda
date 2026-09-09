{-# OPTIONS --safe #-}
module Exotic.ERL.MLPTemporalComposition_v150 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl; sym; cong; trans)

------------------------------------------------------------------------
-- Minimal finite algebraic temporal boundary for the stateless MLP variant.
-- The MLP itself is an arbitrary pure function; the theorem therefore does
-- not assume differentiability or real analysis. Temporal composition is
-- carried entirely by an explicitly associative finite accumulator.
------------------------------------------------------------------------

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

appendV : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
appendV [] ys = ys
appendV (x ∷ xs) ys = x ∷ appendV xs ys

------------------------------------------------------------------------
-- A temporal accumulator is any associative binary operation with a unit.
------------------------------------------------------------------------

record Monoid : Set₁ where
  field
    Carrier : Set
    neutral : Carrier
    _∙_ : Carrier → Carrier → Carrier
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    neutralL : ∀ x → neutral ∙ x ≡ x
    neutralR : ∀ x → x ∙ neutral ≡ x

open Monoid

foldV : ∀ (M : Monoid) → ∀ n → Vec (Carrier M) n → Carrier M
foldV M zero [] = neutral M
foldV M (suc n) (x ∷ xs) =
  Monoid._∙_ M x (foldV M n xs)

foldAppend : ∀ {m n} (M : Monoid)
  (xs : Vec (Carrier M) m)
  (ys : Vec (Carrier M) n) →
  foldV M (m + n) (appendV xs ys) ≡
  Monoid._∙_ M (foldV M m xs) (foldV M n ys)
foldAppend M [] ys =
  sym (Monoid.neutralL M (foldV M _ ys))
foldAppend M (x ∷ xs) ys =
  trans
    (cong (Monoid._∙_ M x) (foldAppend M xs ys))
    (sym (Monoid.assoc M x (foldV M _ xs) (foldV M _ ys)))

------------------------------------------------------------------------
-- MLP temporal map/fold. An MLP is stateless, so each timestep receives
-- the same pure network function independently. Temporal chunks therefore
-- compose by ordinary monoid fold.
------------------------------------------------------------------------

record MLP (X Y : Set) : Set where
  field
    forward : X → Y

mlpTemporalFold : ∀ {X n} (M : Monoid) →
  MLP X (Carrier M) →
  Vec X n →
  Carrier M
mlpTemporalFold M net xs =
  foldV M _ (mapV (MLP.forward net) xs)

mlpTemporalComposition : ∀ {X m n} (M : Monoid)
  (net : MLP X (Carrier M))
  (xs : Vec X m)
  (ys : Vec X n) →
  mlpTemporalFold M net (appendV xs ys) ≡
  Monoid._∙_ M
    (mlpTemporalFold M net xs)
    (mlpTemporalFold M net ys)
mlpTemporalComposition M net xs ys =
  foldAppend M (mapV (MLP.forward net) xs)
    (mapV (MLP.forward net) ys)

------------------------------------------------------------------------
-- The network map itself preserves temporal append.
------------------------------------------------------------------------

mlpMapAppend : ∀ {X Y m n}
  (net : MLP X Y)
  (xs : Vec X m)
  (ys : Vec X n) →
  mapV (MLP.forward net) (appendV xs ys) ≡
  appendV (mapV (MLP.forward net) xs) (mapV (MLP.forward net) ys)
mlpMapAppend net [] ys = refl
mlpMapAppend net (x ∷ xs) ys =
  cong (λ zs → MLP.forward net x ∷ zs)
    (mlpMapAppend net xs ys)

------------------------------------------------------------------------
-- Finite normal form for temporal batching: map once per timestep, fold
-- each chunk, then combine the chunk results.
------------------------------------------------------------------------

mlpTemporalNormalForm : ∀ {X m n} (M : Monoid)
  (net : MLP X (Carrier M))
  (xs : Vec X m)
  (ys : Vec X n) →
  mlpTemporalFold M net (appendV xs ys) ≡
  Monoid._∙_ M
    (mlpTemporalFold M net xs)
    (mlpTemporalFold M net ys)
mlpTemporalNormalForm = mlpTemporalComposition
