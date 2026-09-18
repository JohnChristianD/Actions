{-# OPTIONS --safe #-}
module Data.Fin.Pigeonhole where

open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin)
open import Data.Nat using (_<_)
open import Data.Product using (∃₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Fin.Properties using (pigeonhole)

-- If the codomain has fewer Fin points than the domain, a collision exists.
pigeonhole-collision :
  ∀ {m n : Nat} →
  m < n →
  (f : Fin n → Fin m) →
  ∃₂ λ i j → i < j × f i ≡ f j
pigeonhole-collision = pigeonhole
