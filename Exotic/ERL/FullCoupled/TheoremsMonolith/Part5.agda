{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith.Part5 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _≤_; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-injective; toℕ-fromℕ<)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
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
  finiteRational 0 (d ∸ support) d

exactSupportSparsity-law :
  ∀ {d} v support bound →
  exactSupportSparsity v support bound
  ≡ finiteRational 0 (d ∸ support) d
exactSupportSparsity-law v support bound = refl

------------------------------------------------------------------------
-- General finite-action Tsallis-2 near-sparsity.
--
-- The canonical learner currently has a two-action sparsemax specialization,
-- but the exact Tsallis-2 measure is action-cardinality polymorphic.  For
-- weights w : Fin d -> Nat, S = sum w and Q = sum (w²),
--
--   Tsallis2(w) = 1 - S² / (d Q)
--               = (d Q - S²) / (d Q)
--
-- with the zero-vector convention equal to 1.  No logarithm, exponential,
-- floating point, or two-action restriction is used by this definition.
------------------------------------------------------------------------

ActionWeights : Nat → Set
ActionWeights d = Fin d → Nat

nonzeroWeight : Nat → Nat
nonzeroWeight zero = zero
nonzeroWeight (suc _) = suc zero

actionSupportCount : ∀ {d : Nat} → ActionWeights d → Nat
actionSupportCount {zero} _ = zero
actionSupportCount {suc d} v =
  nonzeroWeight (v Data.Fin.zero)
  + actionSupportCount (λ i → v (Data.Fin.suc i))

actionWeightSum : ∀ {d : Nat} → ActionWeights d → Nat
actionWeightSum {zero} _ = zero
actionWeightSum {suc d} v =
  v Data.Fin.zero
  + actionWeightSum (λ i → v (Data.Fin.suc i))

actionWeightSquareSum : ∀ {d : Nat} → ActionWeights d → Nat
actionWeightSquareSum {zero} _ = zero
actionWeightSquareSum {suc d} v =
  (v Data.Fin.zero * v Data.Fin.zero)
  + actionWeightSquareSum (λ i → v (Data.Fin.suc i))

nat-suc-not-zero : ∀ n → suc n ≢ zero
nat-suc-not-zero n ()

generalTsallis2Denominator :
  ∀ {d : Nat} → ActionWeights d → Nat
generalTsallis2Denominator {d} v =
  d * actionWeightSquareSum v

generalTsallis2Numerator :
  ∀ {d : Nat} → ActionWeights d → Nat
generalTsallis2Numerator {d} v =
  generalTsallis2Denominator v
  ∸
  (actionWeightSum v * actionWeightSum v)

generalTsallis2NearSparsity :
  ∀ {d : Nat} → ActionWeights d → C.FiniteRational
generalTsallis2NearSparsity {zero} v =
  C.finiteRational 1 1 1
generalTsallis2NearSparsity {suc d} v with actionWeightSquareSum v
... | zero = C.finiteRational 1 1 1
... | suc q =
  C.finiteRational
    1
    (generalTsallis2Numerator v)
    (generalTsallis2Denominator v)

generalTsallis2NearSparsity-zero :
  ∀ {d : Nat} (v : ActionWeights d) →
  actionWeightSquareSum v ≡ zero →
  generalTsallis2NearSparsity v ≡ C.finiteRational 1 1 1
generalTsallis2NearSparsity-zero v h with actionWeightSquareSum v
... | zero = refl
... | suc q = ⊥-elim (nat-suc-not-zero q h)

generalTsallis2NearSparsity-definition :
  ∀ {d : Nat} (v : ActionWeights d) →
  actionWeightSquareSum v ≢ zero →
  generalTsallis2NearSparsity v
  ≡ C.finiteRational
      1
      (generalTsallis2Numerator v)
      (generalTsallis2Denominator v)
generalTsallis2NearSparsity-definition {zero} v h =
  ⊥-elim (h refl)
generalTsallis2NearSparsity-definition {suc d} v h with actionWeightSquareSum v
... | zero = ⊥-elim (h refl)
... | suc q = refl

------------------------------------------------------------------------
-- Exact support sparsity and Tsallis-2 share the same support boundary.
-- The canonical hard measure is (d-k)/d; the generalized Tsallis-2 measure
-- is a weighted effective-support quantity.  Equality at the hard boundary
-- is characterized by the uniform-on-support identity S² = k Q.
------------------------------------------------------------------------

generalSupportSparsity :
  ∀ {d : Nat} → ActionWeights d → FiniteRational
generalSupportSparsity {d} v =
  C.finiteRational 0
    (d ∸ actionSupportCount v)
    d

generalSupportSparsity-definition :
  ∀ {d : Nat} (v : ActionWeights d) →
  generalSupportSparsity v
  ≡ C.finiteRational 0
      (d ∸ actionSupportCount v)
      d
generalSupportSparsity-definition v = refl

record UniformSupportTsallisBoundary
  (d : Nat) (v : ActionWeights d) : Set₁ where
  constructor uniformSupportTsallisBoundary
  field
    support : Nat
    supportLaw : support ≡ actionSupportCount v
    uniformSquareLaw :
      actionWeightSum v * actionWeightSum v
      ≡ support * actionWeightSquareSum v

------------------------------------------------------------------------
-- The existing two-action carrier is retained as a canonical specialization,
-- not as the definition of the Tsallis-2 measure.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Exact Tsallis-2 near-sparsity.
--
-- Shannon log/exp is intentionally absent from the executable theorem
-- surface.  For the two-action carrier, pᵢ = wᵢ / S gives
--
--   1 - 1 / (2 * sum pᵢ²)
-- = (2 * sum wᵢ² - S²) / (2 * sum wᵢ²).
--
-- The theorem records this value by an exact cleared-denominator
-- FiniteRational pair.  It therefore needs no transcendental or floating
-- analysis.  The zero-vector convention is exact and explicit.
------------------------------------------------------------------------

tsallis2SupportBit : Nat → Nat
tsallis2SupportBit zero = zero
tsallis2SupportBit (suc n) = suc zero

tsallis2ExactSparsityPair : Nat → Nat → C.FiniteRational
tsallis2ExactSparsityPair a b =
  C.finiteRational
    1
    (suc (suc zero) ∸
      (tsallis2SupportBit a + tsallis2SupportBit b))
    (suc (suc zero))

tsallis2PairSum : Nat → Nat → Nat
tsallis2PairSum a b = a + b

tsallis2PairSquareSum : Nat → Nat → Nat
tsallis2PairSquareSum a b = (a * a) + (b * b)

tsallis2PairDenominator : Nat → Nat → Nat
tsallis2PairDenominator a b =
  suc (suc zero) * tsallis2PairSquareSum a b

tsallis2PairNumerator : Nat → Nat → Nat
tsallis2PairNumerator a b =
  tsallis2PairDenominator a b ∸
    (tsallis2PairSum a b * tsallis2PairSum a b)

tsallis2NearSparsityPair : Nat → Nat → C.FiniteRational
tsallis2NearSparsityPair zero zero =
  C.finiteRational 1 1 1
tsallis2NearSparsityPair zero (suc b) =
  C.finiteRational
    1
    (tsallis2PairNumerator zero (suc b))
    (tsallis2PairDenominator zero (suc b))
tsallis2NearSparsityPair (suc a) b =
  C.finiteRational
    1
    (tsallis2PairNumerator (suc a) b)
    (tsallis2PairDenominator (suc a) b)

fractionEquivalent : C.FiniteRational → C.FiniteRational → Set
fractionEquivalent x y =
  (C.numerator x * C.denominator y)
  ≡
  (C.numerator y * C.denominator x)

tsallis2Exact-oneHot128 :
  tsallis2ExactSparsityPair 128 0
  ≡ C.finiteRational 1 1 2
tsallis2Exact-oneHot128 = refl

tsallis2Near-oneHot128 :
  fractionEquivalent
    (tsallis2NearSparsityPair 128 0)
    (C.finiteRational 1 1 2)
tsallis2Near-oneHot128 = refl

tsallis2Near-exact-oneHot128 :
  fractionEquivalent
    (tsallis2NearSparsityPair 128 0)
    (tsallis2ExactSparsityPair 128 0)
tsallis2Near-exact-oneHot128 = refl

canonicalPolicyExactSparsity :
  ∀ K s →
  C.FiniteRational
canonicalPolicyExactSparsity K s with C.canonicalPolicy K s
... | l , r =
  tsallis2ExactSparsityPair
    (toℕ (C.code l))
    (toℕ (C.code r))

canonicalPolicyTsallis2NearSparsity :
  ∀ K s →
  C.FiniteRational
canonicalPolicyTsallis2NearSparsity K s with C.canonicalPolicy K s
... | l , r =
  tsallis2NearSparsityPair
    (toℕ (C.code l))
    (toℕ (C.code r))

------------------------------------------------------------------------
-- Temporal hard/near sparsity preservation.
--
-- The full learner changes Watkins critic and LCB counts, so an unconditional
-- policy-support invariant would be unsound.  The exact theorem required for
-- the closed loop is therefore: one-step closure implies all finite prefixes
-- by induction.
------------------------------------------------------------------------

canonicalHardSparse-normOptimizer-temporal-invariance :
  ∀ K s n o →
  C.HardSparseLeft (C.canonicalPolicy K s) →
  C.HardSparseLeft
    (C.canonicalPolicy K
      (C.replaceNorm (C.replaceOptimizer s o) n))
canonicalHardSparse-normOptimizer-temporal-invariance =
  C.hardSparse-composition-normPair-F4-L2

canonicalHardSparsityLeft-fullLoop-preservation :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState) →
  C.HardSparseLeft (C.canonicalPolicy K s) →
  (∀ n →
     C.HardSparseLeft
       (C.canonicalPolicy K (C.iterateCanonical K n s)) →
     C.HardSparseLeft
       (C.canonicalPolicy K
         (C.iterateCanonical K (suc n) s))) →
  ∀ n →
  C.HardSparseLeft
    (C.canonicalPolicy K (C.iterateCanonical K n s))
canonicalHardSparsityLeft-fullLoop-preservation K s base closed zero =
  base
canonicalHardSparsityLeft-fullLoop-preservation K s base closed (suc n) =
  closed n
    (canonicalHardSparsityLeft-fullLoop-preservation
      K s base closed n)

canonicalExactSparsity-fullLoop-preservation :
  ∀ K s →
  (∀ n →
     canonicalPolicyExactSparsity K
       (C.iterateCanonical K (suc n) s)
     ≡
     canonicalPolicyExactSparsity K
       (C.iterateCanonical K n s)) →
  ∀ n →
  canonicalPolicyExactSparsity K
    (C.iterateCanonical K n s)
  ≡
  canonicalPolicyExactSparsity K s
canonicalExactSparsity-fullLoop-preservation K s closed zero = refl
canonicalExactSparsity-fullLoop-preservation K s closed (suc n) =
  trans
    (closed n)
    (canonicalExactSparsity-fullLoop-preservation K s closed n)

canonicalTsallis2NearSparsity-fullLoop-preservation :
  ∀ K s →
  (∀ n →
     canonicalPolicyTsallis2NearSparsity K
       (C.iterateCanonical K (suc n) s)
     ≡
     canonicalPolicyTsallis2NearSparsity K
       (C.iterateCanonical K n s)) →
  ∀ n →
  canonicalPolicyTsallis2NearSparsity K
    (C.iterateCanonical K n s)
  ≡
  canonicalPolicyTsallis2NearSparsity K s
canonicalTsallis2NearSparsity-fullLoop-preservation K s closed zero = refl
canonicalTsallis2NearSparsity-fullLoop-preservation K s closed (suc n) =
  trans
    (closed n)
    (canonicalTsallis2NearSparsity-fullLoop-preservation K s closed n)

record TemporalNearSparsityInvariant : Set₁ where
  constructor temporalNearSparsityInvariant
  field
    measure : C.FullLearnerState → C.FiniteRational
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
-- Exact compressed-summary homomorphism and prediction=compression.
--
-- A smaller summary is sound exactly when its decoder reconstructs the
-- original endomorphism on the relevant state.  The scan theorem below
-- separates the algebraic homomorphism from that semantic decoder law.
------------------------------------------------------------------------

record CompositionalSummary (State Summary : Set) : Set₁ where
  constructor compositionalSummary
  field
    identitySummary : Summary
    composeSummary : Summary → Summary → Summary
    compressSummary : C.Endomorphism State → Summary
    summaryIdentity :
      compressSummary C.identityEndomorphism ≡ identitySummary
    summaryComposition :
      ∀ f g →
      compressSummary
        (C.composeEndomorphism f g)
      ≡
      composeSummary
        (compressSummary f)
        (compressSummary g)

open CompositionalSummary public

endomorphismPower :
  ∀ {State : Set} →
  C.Endomorphism State →
  Nat →
  C.Endomorphism State
endomorphismPower f zero = C.identityEndomorphism
endomorphismPower f (suc n) =
  C.composeEndomorphism
    (endomorphismPower f n)
    f

compressedPower :
  ∀ {State Summary : Set} →
  CompositionalSummary State Summary →
  C.Endomorphism State →
  Nat →
  Summary
compressedPower M f zero = identitySummary M
compressedPower M f (suc n) =
  composeSummary M
    (compressedPower M f n)
    (compressSummary M f)

compressedPower-scan :
  ∀ {State Summary : Set}
  (M : CompositionalSummary State Summary)
  (f : C.Endomorphism State) →
  ∀ n →
  compressSummary M (endomorphismPower f n)
  ≡
  compressedPower M f n
compressedPower-scan M f zero = summaryIdentity M
compressedPower-scan M f (suc n) =
  trans
    (summaryComposition M
      (endomorphismPower f n)
      f)
    (cong₂
      (composeSummary M)
      (compressedPower-scan M f n)
      refl)

exactPredictionEqualsCompressed :
  ∀ {State Summary Output : Set}
  (M : CompositionalSummary State Summary)
  (decode : Summary → C.Endomorphism State) →
  (correct :
    ∀ f s →
      C.applyEndomorphism
        (decode (compressSummary M f))
        s
      ≡
      C.applyEndomorphism f s) →
  ∀ (target : State → Output)
    (f : C.Endomorphism State)
    (s : State) →
  target (C.applyEndomorphism f s)
  ≡
  target
    (C.applyEndomorphism
      (decode (compressSummary M f))
      s)
exactPredictionEqualsCompressed M decode correct target f s =
  sym (cong target (correct f s))

------------------------------------------------------------------------
-- Polynomial / rational / Möbius / finite-Taylor upper-order composition.
--
-- Each layer is an independently closed summary carrier.  Their product is
-- itself a closed summary carrier, and the product compression law is
-- proved componentwise.  This is the exact structural theorem required
-- before choosing concrete coefficient representations.
------------------------------------------------------------------------

record SummaryLayer (State Summary : Set) : Set₁ where
  constructor summaryLayer
  field
    layerIdentity : Summary
    layerCompose : Summary → Summary → Summary
    layerCompress : C.Endomorphism State → Summary
    layerComposition :
      ∀ f g →
      layerCompress (C.composeEndomorphism f g)
      ≡
      layerCompose (layerCompress f) (layerCompress g)

UpperOrderSummary :
  ∀ {P R M T : Set} → Set
UpperOrderSummary {P = P} {R = R} {M = M} {T = T} =
  P × (R × (M × T))

upperOrderCompose :
  ∀ {State P R M T : Set} →
  SummaryLayer State P →
  SummaryLayer State R →
  SummaryLayer State M →
  SummaryLayer State T →
  UpperOrderSummary {P = P} {R = R} {M = M} {T = T} →
  UpperOrderSummary {P = P} {R = R} {M = M} {T = T} →
  UpperOrderSummary {P = P} {R = R} {M = M} {T = T}
upperOrderCompose P R M T
  (p₁ , (r₁ , (m₁ , t₁)))
  (p₂ , (r₂ , (m₂ , t₂))) =
  SummaryLayer.layerCompose P p₁ p₂ ,
  (SummaryLayer.layerCompose R r₁ r₂ ,
    (SummaryLayer.layerCompose M m₁ m₂ ,
      SummaryLayer.layerCompose T t₁ t₂))

upperOrderCompress :
  ∀ {State P R M T : Set} →
  SummaryLayer State P →
  SummaryLayer State R →
  SummaryLayer State M →
  SummaryLayer State T →
  C.Endomorphism State →
  UpperOrderSummary {P = P} {R = R} {M = M} {T = T}
upperOrderCompress P R M T f =
  SummaryLayer.layerCompress P f ,
  (SummaryLayer.layerCompress R f ,
    (SummaryLayer.layerCompress M f ,
      SummaryLayer.layerCompress T f))

upperOrderComposition-homomorphism :
  ∀ {State P R M T : Set}
  (P : SummaryLayer State P)
  (R : SummaryLayer State R)
  (M : SummaryLayer State M)
  (T : SummaryLayer State T) →
  ∀ f g →
  upperOrderCompress P R M T (C.composeEndomorphism f g)
  ≡
  upperOrderCompose P R M T
    (upperOrderCompress P R M T f)
    (upperOrderCompress P R M T g)
upperOrderComposition-homomorphism P R M T f g =
  cong₂
    (λ p q → p , q)
    (SummaryLayer.layerComposition P f g)
    (cong₂
      (λ r q → r , q)
      (SummaryLayer.layerComposition R f g)
      (cong₂
        (λ m t → m , t)
        (SummaryLayer.layerComposition M f g)
        (SummaryLayer.layerComposition T f g)))

record UpperOrderRepresentationTheorem
  (State Polynomial Rational Mobius Taylor : Set) : Set₁ where
  constructor upperOrderRepresentationTheorem
  field
    polynomialLayer : SummaryLayer State Polynomial
    rationalLayer : SummaryLayer State Rational
    mobiusLayer : SummaryLayer State Mobius
    taylorUpperOrderLayer : SummaryLayer State Taylor
    compositionRepresentation :
      ∀ f g →
      upperOrderCompress
        polynomialLayer rationalLayer mobiusLayer taylorUpperOrderLayer
        (C.composeEndomorphism f g)
      ≡
      upperOrderCompose
        polynomialLayer rationalLayer mobiusLayer taylorUpperOrderLayer
        (upperOrderCompress
          polynomialLayer rationalLayer mobiusLayer taylorUpperOrderLayer f)
        (upperOrderCompress
          polynomialLayer rationalLayer mobiusLayer taylorUpperOrderLayer g)

upperOrderRepresentationTheorem-from-layers :
  ∀ {State Polynomial Rational Mobius Taylor : Set}
  (P : SummaryLayer State Polynomial)
  (R : SummaryLayer State Rational)
  (M : SummaryLayer State Mobius)
  (T : SummaryLayer State Taylor) →
  UpperOrderRepresentationTheorem State Polynomial Rational Mobius Taylor
upperOrderRepresentationTheorem-from-layers P R M T =
  upperOrderRepresentationTheorem
    P R M T
    (upperOrderComposition-homomorphism P R M T)

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
