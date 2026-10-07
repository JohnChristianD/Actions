{-# OPTIONS --guarded #-}

module FullCoupled.Guarded.TypeTopologyUnsafe where

open import Unsafe.CoNat-Equiv using
  ( CoNat
  ; CoNat≈ℕ∞
  ; CoNat-equality-criterion
  ; ＝C
  )

TypeTopologyCoNat : Set
TypeTopologyCoNat = CoNat

TypeTopologyCoNatEquivalence :
  ∀
  → CoNat≈ℕ∞
  → CoNat≈ℕ∞
TypeTopologyCoNatEquivalence e = e

coNatCriterion :
  ∀ (x y : CoNat) →
  ((n : ℕ) → CoNat-to-ℕ→𝟚 x n ＝ CoNat-to-ℕ→𝟚 y n) →
  ＝C x y
coNatCriterion = CoNat-equality-criterion
