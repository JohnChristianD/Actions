{-# OPTIONS --safe #-}
module Exotic.ERL.MLPTemporalComposition_v150 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)

------------------------------------------------------------------------
-- Minimal finite algebraic temporal boundary for the stateless MLP variant.
-- The MLP itself is an arbitrary pure function; the theorem therefore does
-- not assume differentiability or real analysis.  Temporal composition is
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

foldV : ∀ {M} → Monoid M → ∀ n → Vec (Carrier M) n → Carrier M
foldV M zero [] = neutral M
foldV M (suc n) (x ∷ xs) = x ∙ foldV M n xs
  where
    _∙_ = Monoid._∙_ M

foldAppend : ∀ {M m n}
  (M₀ : Monoid M)
  (xs : Vec (Monoid.Carrier M₀) m)
  (ys : Vec (Monoid.Carrier M₀) n) →
  foldV M₀ (m + n) (appendV xs ys) ≡
  foldV M₀ m xs ∙ foldV M₀ n ys
foldAppend M₀ [] ys = sym-neutralLeft M₀ ys
  where
  sym-neutralLeft : ∀ (N : Monoid M) (zs : Vec (Carrier N) n) →
    foldV N n zs ≡ neutral N ∙ foldV N n zs
  sym-neutralLeft N zs = sym (neutralL N (foldV N _ zs))
foldAppend M₀ (x ∷ xs) ys =
  trans
    (cong (λ z → Monoid._∙_ M₀ x z) (foldAppend M₀ xs ys))
    (sym (assoc M₀ x (foldV M₀ _ xs) (foldV M₀ _ ys)))

------------------------------------------------------------------------
-- MLP temporal map/fold.  An MLP is stateless, so each timestep receives
-- the same pure network function independently.  Temporal chunks therefore
-- compose by ordinary monoid fold.
------------------------------------------------------------------------

record MLP (X Y : Set) : Set where
  field
    forward : X → Y

mlpTemporalFold : ∀ {M X Y n}
  (M₀ : Monoid M) →
  MLP X (Carrier M₀) →
  Vec X n →
  Carrier M₀
mlpTemporalFold M₀ net xs =
  foldV M₀ _ (mapV (MLP.forward net) xs)

mlpTemporalComposition : ∀ {M X Y m n}
  (M₀ : Monoid M)
  (net : MLP X (Carrier M₀))
  (xs : Vec X m)
  (ys : Vec X n) →
  mlpTemporalFold M₀ net (appendV xs ys) ≡
  Monoid._∙_ M₀
    (mlpTemporalFold M₀ net xs)
    (mlpTemporalFold M₀ net ys)
mlpTemporalComposition M₀ net xs ys =
  foldAppend M₀ (mapV (MLP.forward net) xs)
    (mapV (MLP.forward net) ys)

------------------------------------------------------------------------
-- The stronger chunk law: the network map itself distributes over temporal
-- append before the monoid fold is applied.
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
-- Hence MLP temporal batching has a finite compositional normal form:
-- map once per timestep, then fold each chunk, then combine chunk states.
------------------------------------------------------------------------

mlpTemporalNormalForm : ∀ {M X Y m n}
  (M₀ : Monoid M)
  (net : MLP X (Carrier M₀))
  (xs : Vec X m)
  (ys : Vec X n) →
  mlpTemporalFold M₀ net (appendV xs ys) ≡
  Monoid._∙_ M₀
    (mlpTemporalFold M₀ net xs)
    (mlpTemporalFold M₀ net ys)
mlpTemporalNormalForm = mlpTemporalComposition
