{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.Int8StabilityComposition where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)

Fixed : ∀ {S : Set} → (S → S) → S → Set
Fixed step s = step s ≡ s

record LyapunovCertificate (S : Set) (step : S → S) : Set₁ where
  constructor lyapunovCertificate
  field
    energy : S → Nat
    strictDecrease : ∀ s → step s ≢ s → energy (step s) < energy s

open LyapunovCertificate public

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate step zero s = s
iterate step (suc n) s = step (iterate step n s)

iterate-shift :
  ∀ {S : Set} (step : S → S) (n : Nat) (s : S) →
  iterate step n (step s) ≡ iterate step (suc n) s
iterate-shift step zero s = refl
iterate-shift step (suc n) s = cong step (iterate-shift step n s)

OrbitNonFixed :
  ∀ {S : Set} {step : S → S} → S → Set
OrbitNonFixed {step = step} s =
  ∀ n → iterate step n s ≢ step (iterate step n s)

shiftOrbitNonFixed :
  ∀ {S : Set} {step : S → S} {s : S} →
  OrbitNonFixed s → OrbitNonFixed (step s)
shiftOrbitNonFixed {step = step} {s = s} nf n =
  let p = iterate-shift step n s
  in nf (suc n)
       (λ eq → nf (suc n) (trans (sym p) (trans eq (cong step p))))

lt-trans-nat :
  ∀ {a b c : Nat} → a < b → b < c → a < c
lt-trans-nat (s≤s p) (s≤s q) =
  s≤s (le-trans-nat p q)
  where
  le-trans-nat :
    ∀ {m n k : Nat} → m ≤ n → n ≤ k → m ≤ k
  le-trans-nat z≤n r = r
  le-trans-nat (s≤s l) (s≤s r) = s≤s (le-trans-nat l r)

iterate-energy-decrease :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step)
  {s : S} →
  OrbitNonFixed s →
  ∀ n →
  energy L (iterate step (suc n) s) < energy L s
iterate-energy-decrease L {s = s} nf zero =
  strictDecrease L s (nf zero)
iterate-energy-decrease L {s = s} nf (suc n) =
  lt-trans-nat
    (subst
      (λ z → energy L z < energy L (step s))
      (iterate-shift step (suc n) s)
      (iterate-energy-decrease L (shiftOrbitNonFixed nf) n))
    (strictDecrease L s (nf zero))

noNontrivialFiniteCycle :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step)
  {s : S} (n : Nat) →
  iterate step (suc n) s ≡ s →
  OrbitNonFixed s →
  ⊥
noNontrivialFiniteCycle L {s = s} n cyc nf =
  less-irrefl (energy L s)
    (subst
      (λ z → energy L z < energy L s)
      cyc
      (iterate-energy-decrease L nf n))
  where
  less-irrefl : ∀ k → ¬ (k < k)
  less-irrefl zero ()
  less-irrefl (suc k) (s≤s p) = less-irrefl k p

gruNoNontrivialFiniteCycle :
  ∀ {S : Set} (step : S → S) (L : LyapunovCertificate S step)
  {s : S} (n : Nat) →
  iterate step (suc n) s ≡ s →
  OrbitNonFixed s →
  ⊥
gruNoNontrivialFiniteCycle step L = noNontrivialFiniteCycle L
