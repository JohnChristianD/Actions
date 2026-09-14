{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.Int8StabilityComposition where

open import Agda.Builtin.Equality using (_≡_; sym; trans; subst)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_<_ ; _≤_; _+_)
open import Data.Nat.Properties using (<-irrefl; <-trans)

------------------------------------------------------------------------
-- Finite/int8-safe convergence layer.
-- Only constructive theorems with real hypotheses are retained here.
------------------------------------------------------------------------

Fixed : ∀ {S : Set} → (S → S) → S → Set
Fixed step s = step s ≡ s

record LyapunovCertificate (S : Set) (step : S → S) : Set₁ where
  constructor lyapunovCertificate
  field
    energy : S → Nat
    strictDecrease : ∀ s → (step s ≢ s) → energy (step s) < energy s

open LyapunovCertificate public

------------------------------------------------------------------------
-- A strict Nat-valued Lyapunov law really does exclude a nontrivial
-- 2-cycle, constructively.
------------------------------------------------------------------------

noNontrivialTwoCycle :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step)
  {s : S} →
  step (step s) ≡ s →
  step s ≢ s →
  ⊥
noNontrivialTwoCycle L {s = s} cyc not-fixed =
  let
    first : energy L (step s) < energy L s
    first = strictDecrease L s not-fixed

    step-not-fixed : step (step s) ≢ step s
    step-not-fixed eq =
      not-fixed (trans (sym eq) cyc)

    second : energy L (step (step s)) < energy L (step s)
    second = strictDecrease L (step s) step-not-fixed

    second' : energy L s < energy L (step s)
    second' =
      subst
        (λ z → energy L z < energy L (step s))
        cyc
        second
  in
    <-irrefl (energy L s) (<-trans second' first)

------------------------------------------------------------------------
-- Finite metric contraction also gives a direct constructive theorem:
-- two distinct fixed points cannot coexist.
------------------------------------------------------------------------

record FiniteMetric (S : Set) : Set₁ where
  constructor finiteMetric
  field
    distance : S → S → Nat
    distance-zero : ∀ x → distance x x ≡ 0
    distance-positive : ∀ {x y} → x ≢ y → 0 < distance x y
    distance-triangle : ∀ x y z → distance x z ≤ distance x y + distance y z

open FiniteMetric public

record ContractionCertificate
  (S : Set)
  (step : S → S)
  (M : FiniteMetric S) : Set₁ where
  constructor contractionCertificate
  field
    contract : ∀ {x y} → x ≢ y →
      distance M (step x) (step y) < distance M x y

open ContractionCertificate public

contractive-no-distinct-fixed :
  ∀ {S : Set} {step : S → S} {M : FiniteMetric S}
  (C : ContractionCertificate S step M)
  {x y : S} →
  Fixed step x →
  Fixed step y →
  x ≢ y →
  ⊥
contractive-no-distinct-fixed C fx fy neq =
  <-irrefl (distance M x y)
    (trans
      (contract C neq)
      (fixed-distance-equality fx fy))
  where
  fixed-distance-equality :
    ∀ {u v : S} →
    Fixed step u →
    Fixed step v →
    distance M (step u) (step v) ≡ distance M u v
  fixed-distance-equality refl refl = refl
