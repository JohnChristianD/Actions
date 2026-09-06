{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage07_OuterFinite where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

maxNat : Nat → Nat → Nat
maxNat zero y = y
maxNat (suc x) zero = suc x
maxNat (suc x) (suc y) = suc (maxNat x y)

record Archive : Set where
  constructor archive
  field
    best : Nat

insert : Nat → Archive → Archive
insert x a = archive (maxNat x (Archive.best a))

insertShape : ∀ x a → Archive.best (insert x a) ≡ maxNat x (Archive.best a)
insertShape x a = refl
