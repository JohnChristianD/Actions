{-# OPTIONS --safe #-}
module Exotic.econlib.GameTheory.GymnaxBernoulliBandit where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Provenance: gymnax misc / BernoulliBandit-misc.
-- This port keeps the environment finite and deterministic by making the
-- Bernoulli outcome an explicit kernel input. It therefore ports the finite
-- decision/reward algebra, not hidden RNG semantics.

record Bandit (Arms : Set) : Set where
  constructor bandit
  field
    reward : Arms → Bool → Nat

BanditTrace : Set → Set
BanditTrace A = Nat × A

step : {A : Set} → Bandit A → A → Bool → Nat
step B a outcome = Bandit.reward B a outcome

rewardBound : {A : Set} → (B : Bandit A) → A → Bool → Nat
rewardBound = Bandit.reward

banditIdentity : {A : Set} → (B : Bandit A) → A → Bool →
  rewardBound B ≡ Bandit.reward B
banditIdentity B a outcome = refl
