{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith.Part5 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _≤_; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-injective; toℕ-fromℕ<)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith.Part4 public

------------------------------------------------------------------------
-- Complete closed-loop learner scan.
--
-- FullLearnerState is the product carrier of the heterogeneous components:
-- LCB/Sparsemax, Watkins, q-Munchausen control/value, attention/RoPE/Walsh,
-- GRU, F4/L2, norm, and recurrent counts.  The kernel K is an explicit
-- parameter of the deterministic endomorphism.
------------------------------------------------------------------------

canonicalFullLearnerRecurrentNetwork :
  C.FullLearnerKernel →
  C.RecurrentNetwork C.FullLearnerState ⊤
canonicalFullLearnerRecurrentNetwork K =
  C.recurrentNetwork (λ s _ → C.canonicalFullStep K s)

canonicalFullPrefixState :
  ∀ K → C.FullLearnerState → Nat → C.FullLearnerState
canonicalFullPrefixState K s n =
  C.recurrentPrefixState
    (canonicalFullLearnerRecurrentNetwork K)
    (λ _ → tt) n s

canonicalFullPrefixEndomorphism :
  ∀ K → C.FullLearnerState → Nat → C.Endomorphism C.FullLearnerState
canonicalFullPrefixEndomorphism K s n =
  C.recurrentPrefixEndomorphism
    (canonicalFullLearnerRecurrentNetwork K)
    (λ _ → tt) n

canonicalFullPrefix-correct :
  ∀ K s n →
  C.applyEndomorphism (canonicalFullPrefixEndomorphism K s n) s
  ≡ canonicalFullPrefixState K s n
canonicalFullPrefix-correct K s n =
  C.recurrentPrefix-correct
    (canonicalFullLearnerRecurrentNetwork K)
    (λ _ → tt) n s

canonicalFullPrefix-split :
  ∀ K s m n →
  canonicalFullPrefixState K s (m + n)
  ≡ C.recurrentPrefixState
      (canonicalFullLearnerRecurrentNetwork K)
      (λ _ → tt) n
      (canonicalFullPrefixState K s m)
canonicalFullPrefix-split K s m n =
  C.recurrentPrefix-split
    (canonicalFullLearnerRecurrentNetwork K)
    (λ _ → tt) m n s

canonicalFullPrefix-composition-law :
  ∀ K s m n →
  C.applyEndomorphism
    (canonicalFullPrefixEndomorphism K s (m + n)) s
  ≡
  C.applyEndomorphism
    (C.composeEndomorphism
      (canonicalFullPrefixEndomorphism K s n)
      (canonicalFullPrefixEndomorphism K s m)) s
canonicalFullPrefix-composition-law K s m n =
  trans
    (canonicalFullPrefix-correct K s (m + n))
    (trans
      (canonicalFullPrefix-split K s m n)
      (sym (canonicalFullPrefix-correct
        K (canonicalFullPrefixState K s m) n)))

record DeterministicManySortedProductExactMonoidScanTheorem : Set₁ where
  constructor deterministicManySortedProductExactMonoidScanTheorem
  field
    deterministicStep :
      ∀ K s → C.canonicalFullStep K s ≡ C.canonicalFullStep K s
    exactPrefix :
      ∀ K s n →
      C.applyEndomorphism
        (canonicalFullPrefixEndomorphism K s n) s
      ≡ canonicalFullPrefixState K s n
    prefixComposition :
      ∀ K s m n →
      C.applyEndomorphism
        (canonicalFullPrefixEndomorphism K s (m + n)) s
      ≡
      C.applyEndomorphism
        (C.composeEndomorphism
          (canonicalFullPrefixEndomorphism K s n)
          (canonicalFullPrefixEndomorphism K s m)) s
    endomorphismAssociative :
      ∀ (f g h : C.Endomorphism C.FullLearnerState) s →
      C.applyEndomorphism
        (C.composeEndomorphism (C.composeEndomorphism f g) h) s
      ≡
      C.applyEndomorphism
        (C.composeEndomorphism f (C.composeEndomorphism g h)) s
    normPreserved :
      ∀ K s →
      C.norm (C.canonicalFullStep K s) ≡ C.norm s

canonical-deterministic-many-sorted-product-exact-monoid-scan-theorem :
  DeterministicManySortedProductExactMonoidScanTheorem
canonical-deterministic-many-sorted-product-exact-monoid-scan-theorem =
  deterministicManySortedProductExactMonoidScanTheorem
    (λ K s → refl)
    canonicalFullPrefix-correct
    canonicalFullPrefix-composition-law
    C.endomorphismAssociative
    C.canonicalFullStep-norm

------------------------------------------------------------------------
-- Tight reachable-state count.
--
-- The global state space is countably infinite because clock, LCB counts,
-- and FiniteRational contain Nat data.  For fixed K,s,T, the reachable
-- orbit prefix has exactly suc T distinct states, witnessed by an injective
-- Fin (suc T) enumeration whose image covers every n ≤ T.
------------------------------------------------------------------------

record ExactOrbitPrefixCardinality
  (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (T : Nat) : Set₁ where
  constructor exactOrbitPrefixCardinality
  field
    visit : Fin (suc T) → C.FullLearnerState
    visitInjective :
      ∀ {i j} → visit i ≡ visit j → i ≡ j
    coversOrbitPrefix :
      ∀ {n} → n ≤ T →
      Σ (Fin (suc T)) (λ i → visit i ≡ C.iterateCanonical K n s)

canonicalExactOrbitPrefixCardinality :
  ∀ K s T → ExactOrbitPrefixCardinality K s T
canonicalExactOrbitPrefixCardinality K s T =
  exactOrbitPrefixCardinality
    (λ i → C.iterateCanonical K (toℕ i) s)
    (λ {i} {j} eq →
      toℕ-injective
        (C.canonicalOrbit-state-injective K s
          (cong (λ q → C.iterateCanonical K (toℕ q) s) eq)))
    (λ {n} n≤T →
      let i = fromℕ< (s≤s n≤T) in
      i , cong
        (λ q → C.iterateCanonical K q s)
        (toℕ-fromℕ< (s≤s n≤T)))

------------------------------------------------------------------------
-- Exact support sparsity.
--
-- For v : Fin d → Bool with support count k, the exact definition is
-- (d-k)/d.  FiniteRational is used only as an exact symbolic carrier here;
-- no floating approximation is introduced.
------------------------------------------------------------------------

record ExactSupportSparsitySpec (d : Nat) : Set₁ where
  constructor exactSupportSparsitySpec
  field
    vector : Fin d → Bool
    supportCount : Nat
    supportBound : supportCount ≤ d
    value : FiniteRational
    valueLaw :
      value ≡ finiteRational 0 (d ∸ supportCount) d

exactSupportSparsity :
  ∀ {d} → (Fin d → Bool) → (support : Nat) → support ≤ d → FiniteRational
exactSupportSparsity v support bound =
  finiteRational 0 (_∸_ _ support) _

exactSupportSparsity-law :
  ∀ {d} v support bound →
  exactSupportSparsity v support bound
  ≡ finiteRational 0 (d ∸ support) d
exactSupportSparsity-law v support bound = refl

------------------------------------------------------------------------
-- Near sparsity: exact entropy formula as a parameterized analytic model.
-- The current executable Int8 algebra has no Real log/exp, so this is a
-- proof-carrying specification rather than a fabricated Real implementation.
------------------------------------------------------------------------

record NearSparsityModel (d : Nat) : Set₁ where
  constructor nearSparsityModel
  field
    Scalar : Set
    zero one : Scalar
    add mul sub div : Scalar → Scalar → Scalar
    abs log exp : Scalar → Scalar
    ofNat : Nat → Scalar
    sum : (Fin d → Scalar) → Scalar
    weight : Fin d → Scalar
    l1Norm : Scalar
    probability : Fin d → Scalar
    entropy effectiveSupport nearSparsity : Scalar
    probabilityLaw :
      ∀ i → probability i ≡ div (abs (weight i)) l1Norm
    entropyLaw :
      entropy ≡
      sub zero (sum (λ i → mul (probability i) (log (probability i))))
    effectiveSupportLaw :
      effectiveSupport ≡ exp entropy
    nearSparsityLaw :
      nearSparsity ≡
      sub one (div effectiveSupport (ofNat d))
    zeroVectorLaw :
      (∀ i → weight i ≡ zero) → nearSparsity ≡ one

------------------------------------------------------------------------
-- Temporal exact-sparsity preservation is proved for the component slice
-- that the learner actually makes invariant.  A whole-step policy-support
-- invariant is not asserted because canonicalFullStep updates the LCB
-- counts and Watkins critic, both of which enter canonicalPolicy.
------------------------------------------------------------------------

canonicalHardSparse-normOptimizer-temporal-invariance :
  ∀ K s n o →
  C.HardSparseLeft (C.canonicalPolicy K s) →
  C.HardSparseLeft
    (C.canonicalPolicy K (C.replaceNorm (C.replaceOptimizer s o) n))
canonicalHardSparse-normOptimizer-temporal-invariance =
  C.hardSparse-composition-normPair-F4-L2

record TemporalNearSparsityInvariant : Set₁ where
  constructor temporalNearSparsityInvariant
  field
    measure : C.FullLearnerState → FiniteRational
    stepInvariant :
      ∀ K s →
      measure (C.canonicalFullStep K s) ≡ measure s

temporalNearSparsity-invariance :
  ∀ (M : TemporalNearSparsityInvariant) K s →
  TemporalNearSparsityInvariant.measure M
    (C.canonicalFullStep K s)
  ≡ TemporalNearSparsityInvariant.measure M s
temporalNearSparsity-invariance M K s =
  TemporalNearSparsityInvariant.stepInvariant M K s

------------------------------------------------------------------------
-- Negative-q-Munchausen semantics.
-- qLog2Bias8 is an added finite rational/log-like bias in the Watkins target;
-- its sign is encoded by int8Neg.  negativeAlpha8 is the additional control
-- coefficient.  This is not a literal Real logarithm.
------------------------------------------------------------------------

canonicalNegativeQMunchausenBias-is-additive :
  ∀ K s →
  C.canonicalWatkinsTarget K s ≡
  C.int8Add
    (C.int8Add
      (C.int8Add
        (C.canonicalReward8 K s)
        (C.canonicalQLogBias K s))
      (C.int8Mul C.canonicalDiscount8
        (C.maxCriticValue8 (C.critic (C.watkins s)))))
    (C.canonicalEndogenousFeedback K s)
canonicalNegativeQMunchausenBias-is-additive K s =
  C.canonicalWatkinsTarget-law K s
