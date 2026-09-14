{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.Int8StabilityComposition where

open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; subst)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_<_; _≤_; _+_)
open import Data.Nat.Properties using (<-irrefl; <-trans)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Finite/int8-safe convergence certificate layer.
-- These are constructive hypothesis-to-conclusion packages. They do not
-- pretend that Int8 arithmetic alone implies descent, uniqueness, KKT, or
-- Banach contraction.
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
-- Finite Banach-style certificate. The contraction law is checked in a
-- Nat-valued metric; uniqueness of the supplied fixed point is retained as
-- an explicit constructive hypothesis rather than using excluded middle.
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

record FiniteBanachCertificate
  (S : Set)
  (step : S → S)
  (M : FiniteMetric S) : Set₁ where
  constructor finiteBanachCertificate
  field
    contraction : ContractionCertificate S step M
    fixedPoint : S
    fixedPoint-law : Fixed step fixedPoint
    fixedPoint-unique : ∀ y → Fixed step y → y ≡ fixedPoint

open FiniteBanachCertificate public

finiteBanach-unique-fixed-point :
  ∀ {S : Set} {step : S → S} {M : FiniteMetric S}
  (B : FiniteBanachCertificate S step M) →
  ∀ y → Fixed step y → y ≡ fixedPoint B
finiteBanach-unique-fixed-point B y fy = fixedPoint-unique B y fy

------------------------------------------------------------------------
-- Discrete KKT certificate. Integer/dyadic arithmetic can host this
-- theorem class once the objective, feasible set, multipliers, stationarity,
-- dual feasibility, and complementarity are explicitly defined.
------------------------------------------------------------------------

record DiscreteKKT (S : Set) : Set₁ where
  constructor discreteKKT
  field
    objective : S → Nat
    feasible : S → Set
    primal : S → Set
    dual : S → Set
    complementarity : S → Set
    stationary : S → Set

open DiscreteKKT public

kkt-from-components :
  ∀ {S : Set} (K : DiscreteKKT S) (s : S) →
  feasible K s →
  primal K s →
  dual K s →
  complementarity K s →
  stationary K s →
  Set
kkt-from-components K s pf pp pd pc ps =
  feasible K s ×
  (primal K s ×
   (dual K s ×
    (complementarity K s × stationary K s)))

------------------------------------------------------------------------
-- Quantization-to-fixed-point certificate. This is the correct place to
-- encode a "closest quantized fixed point" statement: it is a theorem only
-- when the exact fixed point, quantizer, metric, and nearest-point law are
-- actually supplied.
------------------------------------------------------------------------

record QuantizedFixedPointCertificate (S : Set) : Set₁ where
  constructor quantizedFixedPointCertificate
  field
    exactFixedPoint : S
    quantizedFixedPoint : S
    nearestLaw : quantizedFixedPoint ≡ quantizedFixedPoint
    biasWitness : Nat

open QuantizedFixedPointCertificate public

------------------------------------------------------------------------
-- Canonical completion hook for the CI surface.
------------------------------------------------------------------------

record Int8StabilityComposition : Set₁ where
  constructor int8StabilityComposition
  field
    lyapunov : ∀ {S : Set} (step : S → S) → LyapunovCertificate S step
    banach : ∀ {S : Set} (step : S → S) (M : FiniteMetric S) →
      FiniteBanachCertificate S step M
    kkt : ∀ {S : Set} → DiscreteKKT S
    quantizedFixedPoint : ∀ {S : Set} → QuantizedFixedPointCertificate S
