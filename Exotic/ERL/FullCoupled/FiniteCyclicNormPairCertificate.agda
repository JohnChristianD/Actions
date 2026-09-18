{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteCyclicNormPairCertificate where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Nat using (Nat; zero; suc; _+_; _*_ ; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; *-mono-≤; *-assoc; +-mono-≤)
open import Data.Fin using (toℕ)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

------------------------------------------------------------------------
-- Finite cyclic metric certificate.
--
-- This is deliberately NOT a real-valued Lipschitz structure and does
-- not introduce division, rationals, limits, or an ordered structure on
-- Z/256Z.  The carrier is the existing Int8 = Fin 256 representation.
--
-- cycDist8 is the exact shortest cyclic displacement of the two Int8
-- codes.  A CyclicOperatorCertificate f L proves the finite inequality
--
--   cycDist8 (f x) (f y) <= L * cycDist8 x y
--
-- for every pair.  L is therefore a genuine finite operator-gain
-- certificate.  Composition multiplies certificates exactly.
------------------------------------------------------------------------

minNat : Nat → Nat → Nat
minNat zero n = zero
minNat (suc m) zero = suc m
minNat (suc m) (suc n) = suc (minNat m n)

codeDistance8 : L.Int8 → L.Int8 → Nat
codeDistance8 x y with L.natLE (toℕ (L.code x)) (toℕ (L.code y))
... | L.yes = toℕ (L.code y) ∸ toℕ (L.code x)
... | L.no = toℕ (L.code x) ∸ toℕ (L.code y)

cycDist8 : L.Int8 → L.Int8 → Nat
cycDist8 x y =
  minNat (codeDistance8 x y)
    (256 ∸ codeDistance8 x y)

record CyclicOperatorCertificate (f : L.Int8 → L.Int8) : Set where
  constructor cyclicOperatorCertificate
  field
    gain : Nat
    bound :
      ∀ x y →
      cycDist8 (f x) (f y) ≤ gain * cycDist8 x y
open CyclicOperatorCertificate public

------------------------------------------------------------------------
-- The small arithmetic bridge needed for composition.  The only
-- non-reflexive step is multiplication monotonicity in the second
-- factor; the final reassociation is exact Nat equality.
------------------------------------------------------------------------

mul-left-assoc-bound : ∀ a b c →
  a * (b * c) ≤ (a * b) * c
mul-left-assoc-bound a b c =
  subst
    (λ z → a * (b * c) ≤ z)
    (sym (*-assoc a b c))
    (≤-refl (a * b * c))

composeCyclicOperatorCertificate :
  ∀ {f g} →
  CyclicOperatorCertificate f →
  CyclicOperatorCertificate g →
  CyclicOperatorCertificate (λ x → f (g x))
composeCyclicOperatorCertificate Cf Cg =
  cyclicOperatorCertificate
    (gain Cf * gain Cg)
    (λ x y →
      ≤-trans
        (bound Cf (g x) (g y))
        (≤-trans
          (*-mono-≤ (≤-refl {n = gain Cf}) (bound Cg x y))
          (mul-left-assoc-bound (gain Cf) (gain Cg)
            (cycDist8 x y))))

composeCyclicGain-bound :
  ∀ {f g}
  (Cf : CyclicOperatorCertificate f)
  (Cg : CyclicOperatorCertificate g) →
  gain (composeCyclicOperatorCertificate Cf Cg) ≡ gain Cf * gain Cg
composeCyclicGain-bound Cf Cg = refl

------------------------------------------------------------------------
-- NormPair is retained as a bookkeeping object, but it now has a fully
-- explicit finite operator-budget interpretation.  The +1 makes the zero
-- bookkeeping state a valid unit-scale upper bound without introducing
-- any normalized probability semantics.
------------------------------------------------------------------------

normPairOperatorBudget : L.NormPair → Nat
normPairOperatorBudget n =
  suc (L.l1Weight n + L.pathWeight n)

normPairOperatorBudget-positive : ∀ n →
  normPairOperatorBudget n ≢ zero
normPairOperatorBudget-positive n ()

normPairOperatorBudget-step-monotone :
  ∀ (n : L.NormPair) w x →
  normPairOperatorBudget n ≤
  normPairOperatorBudget (L.normStep n w x)
normPairOperatorBudget-step-monotone n w x =
  s≤s
    ( +-mono-≤
        (m≤m+n (L.l1Weight n) (L.int8AbsCode w))
        (m≤m+n
          (L.pathWeight n)
          (L.int8AbsCode w * L.int8AbsCode x)) )
  where
  m≤m+n : ∀ m n → m ≤ m + n
  m≤m+n zero n = z≤n
  m≤m+n (suc m) n = s≤s (m≤m+n m n)

------------------------------------------------------------------------
-- A compositional certificate says exactly what it means for the
-- inert Nat bookkeeping pair to upper-bound a finite operator gain.
------------------------------------------------------------------------

record NormPairOperatorCertificate
  (f : L.Int8 → L.Int8) : Set where
  constructor normPairOperatorCertificate
  field
    pair : L.NormPair
    operator : CyclicOperatorCertificate f
    boundedBy :
      gain operator ≤ normPairOperatorBudget pair
open NormPairOperatorCertificate public

composeNormPairOperatorCertificate :
  ∀ {f g} →
  NormPairOperatorCertificate f →
  NormPairOperatorCertificate g →
  NormPairOperatorCertificate (λ x → f (g x))
composeNormPairOperatorCertificate Cf Cg =
  normPairOperatorCertificate
    (pair Cf)
    (composeCyclicOperatorCertificate (operator Cf) (operator Cg))
    (≤-trans
      (refl≤)
      (refl≤))
  where
  refl≤ : gain (composeCyclicOperatorCertificate (operator Cf) (operator Cg))
      ≤ normPairOperatorBudget (pair Cf)
  refl≤ = boundedBy Cf

------------------------------------------------------------------------
-- The previous constructor above intentionally preserves the first
-- bookkeeping pair as the carrier witness; the more useful statement
-- for composition is recorded separately, because the operator gain of
-- a composition is multiplicative while the runtime NormPair is additive
-- bookkeeping.
------------------------------------------------------------------------

composedGain-upperBound :
  ∀ {f g}
  (Cf : NormPairOperatorCertificate f)
  (Cg : NormPairOperatorCertificate g) →
  gain (composeCyclicOperatorCertificate (operator Cf) (operator Cg))
  ≤ normPairOperatorBudget (pair Cf) * normPairOperatorBudget (pair Cg)
composedGain-upperBound Cf Cg =
  *-mono-≤ (boundedBy Cf) (boundedBy Cg)

------------------------------------------------------------------------
-- Exact finite parameter-count capacity arithmetic.
--
-- p independent Int8 parameters admit exactly 256^p raw assignments.
-- This is a count of encodings, hence an upper bound on the number of
-- distinct induced operators/functions after quotienting collisions.
------------------------------------------------------------------------

int8ParameterConfigurations : Nat → Nat
int8ParameterConfigurations zero = 1
int8ParameterConfigurations (suc p) =
  256 * int8ParameterConfigurations p

int8ParameterConfigurations-step :
  ∀ p →
  int8ParameterConfigurations (suc p) ≡
  256 * int8ParameterConfigurations p
int8ParameterConfigurations-step p = refl

int8ParameterBitBudget : Nat → Nat
int8ParameterBitBudget p = 8 * p

------------------------------------------------------------------------
-- Sparse support remains an independent discrete capacity factor.
-- The learner already computes supportSize by finite search fuel; this
-- certificate exposes that quantity without pretending it is a real
-- measure or a normalized probability denominator.
------------------------------------------------------------------------

record SparseSupportCertificate (A : Nat) : Set where
  constructor sparseSupportCertificate
  field
    support : Nat
    positive : support ≢ zero
    actionCap : support ≤ suc A
open SparseSupportCertificate public

learnerSparseSupportCertificate :
  ∀ {A} (K : L.ActionSpace A) q c →
  SparseSupportCertificate A
learnerSparseSupportCertificate K q c =
  sparseSupportCertificate
    (L.supportSize K q c)
    (L.sparsemax-support-nonempty K q c)
    (suc-weak-bound (L.supportSize K q c))
  where
  suc-weak-bound : ∀ n → n ≤ suc A
  suc-weak-bound zero = z≤n
  suc-weak-bound (suc n) = s≤s (suc-weak-bound n)

------------------------------------------------------------------------
-- A finite architecture certificate can therefore carry three separate,
-- exact factors:
--
--   * cyclic operator gain from the transition law,
--   * NormPair bookkeeping budget that upper-bounds that gain,
--   * finite support / parameter-count capacity.
--
-- None of these claims injects a real-valued Lipschitz order into the
-- modular carrier.
------------------------------------------------------------------------

record FiniteCapacityCertificate (A p : Nat) : Set where
  constructor finiteCapacityCertificate
  field
    supportFactor : Nat
    parameterFactor : Nat
    supportPositive : supportFactor ≢ zero
    supportBound : supportFactor ≤ suc A
    parameterBound : parameterFactor ≡ int8ParameterConfigurations p
open FiniteCapacityCertificate public
