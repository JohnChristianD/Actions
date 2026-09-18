{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteCyclicNormPairCertificate where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; *-mono-≤; *-assoc; +-mono-≤)
open import Data.Fin using (toℕ)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

------------------------------------------------------------------------
-- Finite cyclic operator certificate.
--
-- This is NOT a real-valued Lipschitz theorem.  The carrier is the
-- existing Int8 = Fin 256 carrier, and the comparison is entirely in
-- Nat bookkeeping around the cyclic code distance.
--
-- cycDist8 is the shortest cyclic displacement between two Int8 codes.
-- A certificate with gain L proves:
--
--   cycDist8 (f x) (f y) <= L * cycDist8 x y
--
-- for every x,y.  No division, rationals, limits, or ordered ring
-- structure on Z/256Z are introduced.
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
-- Arithmetic bridge used to re-associate a product bound exactly.
------------------------------------------------------------------------

mul-left-assoc-bound : ∀ a b c →
  a * (b * c) ≤ (a * b) * c
mul-left-assoc-bound a b c =
  subst
    (λ z → a * (b * c) ≤ z)
    (sym (*-assoc a b c))
    (≤-refl (a * b * c))

------------------------------------------------------------------------
-- Operator composition is associative at the function level, while
-- finite cyclic gains compose multiplicatively.
------------------------------------------------------------------------

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

composeCyclicGain-law :
  ∀ {f g}
  (Cf : CyclicOperatorCertificate f)
  (Cg : CyclicOperatorCertificate g) →
  gain (composeCyclicOperatorCertificate Cf Cg) ≡
  gain Cf * gain Cg
composeCyclicGain-law Cf Cg = refl

------------------------------------------------------------------------
-- NormPair is inert bookkeeping, but it can now supply an explicit
-- conservative finite operator budget.  The +1 gives the zero state a
-- unit-scale budget without pretending that NormPair stores probabilities.
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
    (+-mono-≤
      (m≤m+n (L.l1Weight n) (L.int8AbsCode w))
      (m≤m+n
        (L.pathWeight n)
        (L.int8AbsCode w * L.int8AbsCode x)))
  where
  m≤m+n : ∀ m n → m ≤ m + n
  m≤m+n zero n = z≤n
  m≤m+n (suc m) n = s≤s (m≤m+n m n)

record NormPairOperatorCertificate
  (f : L.Int8 → L.Int8) : Set where
  constructor normPairOperatorCertificate
  field
    pair : L.NormPair
    operator : CyclicOperatorCertificate f
    boundedBy :
      gain operator ≤ normPairOperatorBudget pair
open NormPairOperatorCertificate public

------------------------------------------------------------------------
-- Composition theorem for the certificate layer.
--
-- The runtime NormPair remains additive bookkeeping.  The theorem does
-- not silently identify that additive pair with the multiplicative
-- operator gain; instead it exposes the exact product bound separately.
------------------------------------------------------------------------

composedGain-upperBound :
  ∀ {f g}
  (Cf : NormPairOperatorCertificate f)
  (Cg : NormPairOperatorCertificate g) →
  gain (composeCyclicOperatorCertificate (operator Cf) (operator Cg))
  ≤ normPairOperatorBudget (pair Cf) *
    normPairOperatorBudget (pair Cg)
composedGain-upperBound Cf Cg =
  *-mono-≤ (boundedBy Cf) (boundedBy Cg)

------------------------------------------------------------------------
-- Exact finite parameter-count arithmetic.
--
-- p independently chosen Int8 parameters have exactly 256^p raw
-- assignments.  Distinct parameter assignments may induce the same
-- transition function, so this is an upper bound on the number of
-- distinct finite operators/hypotheses, not a claim of injectivity.
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
-- Sparse support remains an independent finite capacity factor.
-- The learner already computes supportSize through finite search fuel,
-- and this certificate deliberately exposes the exact support value and
-- its non-emptiness theorem without turning it into a real-valued norm.
------------------------------------------------------------------------

record SparseSupportCertificate
  {A : Nat} (K : L.ActionSpace A) (q : L.QVec A) (c : L.CountVec A) : Set where
  constructor sparseSupportCertificate
  field
    support : Nat
    exactSupport : support ≡ L.supportSize K q c
    positive : support ≢ zero
open SparseSupportCertificate public

learnerSparseSupportCertificate :
  ∀ {A} (K : L.ActionSpace A) q c →
  SparseSupportCertificate K q c
learnerSparseSupportCertificate K q c =
  sparseSupportCertificate
    (L.supportSize K q c)
    refl
    (L.sparsemax-support-nonempty K q c)

learnerNormBudget-step-monotone :
  ∀ {A} (K : L.LearnerKernel A) s reward →
  normPairOperatorBudget (L.normState s) ≤
  normPairOperatorBudget (L.normState (L.learnerStep K s reward))
learnerNormBudget-step-monotone K s reward =
  normPairOperatorBudget-step-monotone
    (L.normState s)
    (L.q s (L.generalPolicy K s))
    shaped
  where
  shaped : L.Int8
  shaped =
    L.int8Add reward
      (L.munchausenSignal
        (L.mode K)
        (L.sparsemaxWeight
          (L.actionSpaceK K)
          (L.q s)
          (L.counts s)
          (L.generalPolicy K s)))

------------------------------------------------------------------------
-- The certificate layer is intentionally orthogonal to the reservoir
-- theorem: it bounds finite transition separation/gain, while the
-- separate reservoir result decides whether a chosen observation map
-- can have a left inverse on the domain.  Hence a finite norm certificate
-- never repairs the existing one-byte full-state collision theorem.
------------------------------------------------------------------------
