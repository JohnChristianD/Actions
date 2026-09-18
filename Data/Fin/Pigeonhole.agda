{-# OPTIONS --safe #-}
module Data.Fin.Pigeonhole where

open import Data.Fin.Properties using (pigeonhole)

-- If the codomain has fewer Fin points than the domain, a collision exists.
pigeonhole-collision :
  ∀ {m n : Nat} →
  m < n →
  (f : Fin n → Fin m) →
  ∃₂ λ i j → i < j × f i ≡ f j
pigeonhole-collision = pigeonhole
