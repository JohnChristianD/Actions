{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith.Part2 where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (NonZero; _∸_; _<_; _≤_; _<ᵇ_; _/_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n; ℕ→Fin-notInjective)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.TheoremsMonolith.Part1 public

------------------------------------------------------------------------
-- Generic equality composition primitive.
--
-- This is theorem algebra, not a learner-specific discovery registry.
-- Automated discovery derives its semantic vocabulary from source
-- declarations; no fixed candidate basis is encoded here.
------------------------------------------------------------------------

record EqualityCompositionTheorem
  {A : Set}
  {x y z : A} : Set where
  constructor equalityCompositionTheorem
  field
    firstStep : x ≡ y
    secondStep : y ≡ z
    composedStep : x ≡ z

composeEqualityTheorem :
  ∀ {A : Set} {x y z : A} →
  x ≡ y →
  y ≡ z →
  EqualityCompositionTheorem
composeEqualityTheorem first second =
  equalityCompositionTheorem
    first
    second
    (trans first second)

------------------------------------------------------------------------
-- Exact recurrent scan class.

--
-- No finite horizon is baked into this theorem. The input is a Nat-indexed
-- stream, and the prefix/split laws quantify over arbitrary natural
-- horizons. The associativity is over endomorphism composition, so the
-- recurrent state transition itself is not approximated or relaxed.
------------------------------------------------------------------------

record RecurrentAssociativeScanTheorem
  (State Input : Set) : Set₁ where
  constructor recurrentAssociativeScanTheorem
  field
    actionAssociative :
      ∀ (f g h : C.Endomorphism State) s →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g)
          h)
        s
      ≡
      C.applyEndomorphism
        (C.composeEndomorphism
          f
          (C.composeEndomorphism g h))
        s

    prefixCorrect :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : Nat → Input)
        (n : Nat)
        (s : State) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism R xs n)
        s
      ≡
      C.recurrentPrefixState R xs n s

    prefixSplit :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : Nat → Input)
        (m n : Nat)
        (s : State) →
      C.recurrentPrefixState R xs (m + n) s
      ≡
      C.recurrentPrefixState
        R
        (C.shiftInput xs m)
        n
        (C.recurrentPrefixState R xs m s)

canonicalGRU-recurrent-associative-scan-theorem :
  RecurrentAssociativeScanTheorem C.GRUState C.Int8
canonicalGRU-recurrent-associative-scan-theorem =
  recurrentAssociativeScanTheorem
    C.endomorphismAssociative
    C.recurrentPrefix-correct
    C.recurrentPrefix-split

------------------------------------------------------------------------
-- Exact prefix work/count semantics.
------------------------------------------------------------------------

recurrentPrefixStepWork : Nat → Nat
recurrentPrefixStepWork zero = zero
recurrentPrefixStepWork (suc n) = suc (recurrentPrefixStepWork n)

recurrentPrefixStepWork-law :
  ∀ n → recurrentPrefixStepWork n ≡ n
recurrentPrefixStepWork-law n = refl

recurrentPrefixStepWork-split :
  ∀ m n →
  recurrentPrefixStepWork (m + n) ≡
  recurrentPrefixStepWork m + recurrentPrefixStepWork n
recurrentPrefixStepWork-split m zero
  rewrite +-identityʳ m = refl
recurrentPrefixStepWork-split m (suc n)
  rewrite +-suc m n =
  cong suc (recurrentPrefixStepWork-split m n)


------------------------------------------------------------------------

canonicalWatkinsTargetSignalStream :
  C.FullLearnerKernel →
  C.FullLearnerState →
  Nat →
  C.Int8
canonicalWatkinsTargetSignalStream K s n =
  C.canonicalWatkinsTarget K
    (C.iterateCanonical K n s)

canonicalWatkinsTarget-recurrent-prefix-correct :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (n : Nat)
  (h : C.GRUState) →
  C.applyEndomorphism
    (C.recurrentPrefixEndomorphism
      C.canonicalGRURecurrentNetwork
      (canonicalWatkinsTargetSignalStream K s)
      n)
    h
  ≡
  C.recurrentPrefixState
    C.canonicalGRURecurrentNetwork
    (canonicalWatkinsTargetSignalStream K s)
    n
    h
canonicalWatkinsTarget-recurrent-prefix-correct K s n h =
  C.recurrentPrefix-correct
    C.canonicalGRURecurrentNetwork
    (canonicalWatkinsTargetSignalStream K s)
    n
    h

------------------------------------------------------------------------
-- Canonical Hadamard/attention/Walsh-Rademacher phase × associative scan
-- composition theorem.
------------------------------------------------------------------------

record CanonicalHadamardAttentionRopePrefixCompositionTheorem : Set₁ where
  constructor canonicalHadamardAttentionRopePrefixCompositionTheorem
  field
    hadamardOrthogonality : C.H4GramLaw
    learnedAttentionComposition :
      ∀ K s →
      C.canonicalAttentionMix K s ≡
      let
        p = C.learnedSparsemaxAttentionWeights (C.attention s)
        w = C.walshHadamardApply (C.liftAttention p)
      in
      C.int8Add
        (C.attentionToGRU K w)
        (C.walshRademacherRopeReadout (C.clock s) w)
    ropePhasePeriod :
      ∀ n w →
      C.walshRademacherRope4 (suc (suc (suc (suc n)))) w
      ≡ C.walshRademacherRope4 n w
    attentionMediator : FiniteAttentionWatkinsGRUF4MediatorTheorem
    associativePrefixScan : RecurrentAssociativeScanTheorem C.GRUState C.Int8
    targetPrefixCorrect :
      ∀ (K : C.FullLearnerKernel) (s : C.FullLearnerState)
      (n : Nat) (h : C.GRUState) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism
          C.canonicalGRURecurrentNetwork
          (canonicalWatkinsTargetSignalStream K s)
          n)
        h
      ≡
      C.recurrentPrefixState
        C.canonicalGRURecurrentNetwork
        (canonicalWatkinsTargetSignalStream K s)
        n h
    exactPrefixWork : ∀ n → recurrentPrefixStepWork n ≡ n
    splitPrefixWork :
      ∀ m n →
      recurrentPrefixStepWork (m + n) ≡
      recurrentPrefixStepWork m + recurrentPrefixStepWork n

open CanonicalHadamardAttentionRopePrefixCompositionTheorem public

canonical-hadamard-attention-rope-prefix-composition-theorem :
  CanonicalHadamardAttentionRopePrefixCompositionTheorem
canonical-hadamard-attention-rope-prefix-composition-theorem =
  canonicalHadamardAttentionRopePrefixCompositionTheorem
    C.walshHadamardOrthogonality4
    (λ K s → learnedAttentionComposition canonical-aq-loop-theorem K s)
    walshRademacherRope4-period4
    finite-attention-watkins-gru-f4-mediator-theorem
    canonicalGRU-recurrent-associative-scan-theorem
    (λ K s n h → canonicalWatkinsTarget-recurrent-prefix-correct K s n h)
    recurrentPrefixStepWork-law
    recurrentPrefixStepWork-split

------------------------------------------------------------------------
-- Explicit equality-composition theorem.
--
-- The e-graph proof-plan combinator is dependency composition.  Actual
-- equality composition is represented separately by composeEqualityTheorem,
-- whose proof term uses trans.  A reflexive identity is never used as the
-- composition theorem itself.
------------------------------------------------------------------------
-- Canonical minimax/Bellman-Shapley inclusion class for the executable
-- biased Watkins + negative-q-Munchausen + L2 target.
--
-- The learner has a concrete Int8 carrier. No ordered ring, interval,
-- metric, or topology is imported here. The inclusion theorem therefore
-- takes the comparison relation and monotone minimax/Bellman-Shapley
-- operator as explicit hypotheses, while the target itself is the exact
-- executable canonicalWatkinsTarget.
------------------------------------------------------------------------

record PointwiseSandwich
  {Input Value : Set}
  (_≤_ : Value → Value → Set)
  (lower actual upper : Input → Value) : Set₁ where
  constructor pointwiseSandwich
  field
    lower≤actual : ∀ x → lower x ≤ actual x
    actual≤upper : ∀ x → actual x ≤ upper x

record MinimaxBellmanShapleyOperator
  (State Value : Set)
  (_≤_ : Value → Value → Set) : Set₁ where
  constructor minimaxBellmanShapleyOperator
  field
    value : (State → Value) → Value
    monotone :
      ∀ (f g : State → Value) →
      (∀ s → f s ≤ g s) →
      value f ≤ value g

record MinimaxBellmanShapleyInclusionTheorem
  (State Value : Set)
  (_≤_ : Value → Value → Set)
  (operator : MinimaxBellmanShapleyOperator State Value _≤_)
  (lower actual upper : State → Value) : Set₁ where
  constructor minimaxBellmanShapleyInclusionTheorem
  field
    lowerBound :
      MinimaxBellmanShapleyOperator.value operator lower
      ≤
      MinimaxBellmanShapleyOperator.value operator actual
    upperBound :
      MinimaxBellmanShapleyOperator.value operator actual
      ≤
      MinimaxBellmanShapleyOperator.value operator upper

open PointwiseSandwich public
open MinimaxBellmanShapleyOperator public
open MinimaxBellmanShapleyInclusionTheorem public

canonicalBiasedWatkinsNegativeQMunchausenL2Target :
  C.FullLearnerKernel → C.FullLearnerState → C.Int8
canonicalBiasedWatkinsNegativeQMunchausenL2Target =
  C.canonicalWatkinsTarget

canonical-qLog2Bias8-law :
  ∀ x →
  C.qLog2Bias8 x ≡
  C.int8Neg
    (C.int8OfNat
      ((C.munchausenScale8 * C.numerator (C.finiteQLog8 x)) /
       C.denominator (C.finiteQLog8 x)))
canonical-qLog2Bias8-law x with toℕ (C.code x)
... | zero = refl
... | suc n = refl

record CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem : Set₁ where
  constructor canonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
  field
    negativeQMunchausenBias :
      ∀ x →
      C.qLog2Bias8 x ≡
      C.int8Neg
        (C.int8OfNat
          ((C.munchausenScale8 * C.numerator (C.finiteQLog8 x)) /
           C.denominator (C.finiteQLog8 x)))

    targetDecomposition :
      ∀ K s →
      canonicalBiasedWatkinsNegativeQMunchausenL2Target K s ≡
      C.int8Add
        (C.int8Add
          (C.int8Add
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          (C.int8Mul
            C.canonicalDiscount8
            (C.maxCriticValue8 (C.critic (C.watkins s)))))
        (C.canonicalEndogenousFeedback K s)

    l2ConsumesTarget :
      ∀ K s →
      C.canonicalOptimizerStep K s ≡
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer s)
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K s)

open CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem public

canonical-biased-watkins-negative-q-munchausen-l2-target-theorem :
  CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
canonical-biased-watkins-negative-q-munchausen-l2-target-theorem =
  canonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
    canonical-qLog2Bias8-law
    (λ K s → C.canonicalWatkinsTarget-law K s)
    (λ K s → C.canonicalOptimizerStep-qMunchausen-L2 K s)

canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class :
  ∀ (K : C.FullLearnerKernel)
  (_≤_ : C.Int8 → C.Int8 → Set)
  (operator :
    MinimaxBellmanShapleyOperator
      C.FullLearnerState
      C.Int8
      _≤_)
  (lower upper : C.FullLearnerState → C.Int8) →
  PointwiseSandwich
    _≤_
    lower
    (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
    upper →
  MinimaxBellmanShapleyInclusionTheorem
    C.FullLearnerState
    C.Int8
    _≤_
    operator
    lower
    (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
    upper
canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class
  K _≤_ operator lower upper
  (pointwiseSandwich lower≤actual actual≤upper) =
  minimaxBellmanShapleyInclusionTheorem
    (monotone operator
      lower
      (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
      lower≤actual)
    (monotone operator
      (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
      upper
      actual≤upper)

------------------------------------------------------------------------
-- Endogenous factorization through a left-invertible observation.
------------------------------------------------------------------------

canonicalWatkinsTarget-endogenous-leftInverse :
  ∀ (K : C.FullLearnerKernel)
  (observe : C.FullLearnerState → C.Int8)
  (inverse : C.Int8 → C.FullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ≡ t) →
  ∀ s →
  C.canonicalWatkinsTarget K s ≡
    C.int8Add
      (C.int8Add
        (C.int8Add
          (C.canonicalReward8 K (inverse (observe s)))
          (C.canonicalQLogBias K (inverse (observe s))))
        (C.int8Mul
          C.canonicalDiscount8
          (C.maxCriticValue8
            (C.critic
              (C.watkins
                (inverse (observe s)))))))
      (C.canonicalEndogenousFeedback K (inverse (observe s)))
canonicalWatkinsTarget-endogenous-leftInverse K observe inverse leftInverse s =
  trans
    (C.canonicalWatkinsTarget-law K s)
    (cong
      (λ t →
        C.int8Add
          (C.int8Add
            (C.int8Add
              (C.canonicalReward8 K t)
              (C.canonicalQLogBias K t))
            (C.int8Mul
              C.canonicalDiscount8
              (C.maxCriticValue8
                (C.critic (C.watkins t)))))
          (C.canonicalEndogenousFeedback K t))
      (leftInverse s))

------------------------------------------------------------------------
-- Infinite-state orbit injectivity and Nat-clock pigeonhole contradiction.
------------------------------------------------------------------------

suc-injective :
  ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

natPlus-left-cancel :
  ∀ (k m n : Nat) → k + m ≡ k + n → m ≡ n
natPlus-left-cancel zero m n eq = eq
natPlus-left-cancel (suc k) m n eq =
  natPlus-left-cancel k m n (suc-injective eq)

canonicalOrbit-state-injective :
  ∀ K s {m n : Nat} →
  C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
  m ≡ n
canonicalOrbit-state-injective K s {m} {n} eq =
  natPlus-left-cancel
    (C.clock s) m n
    (trans
      (sym (C.clockAfter K m s))
      (trans
        (cong (λ t → C.clock t) eq)
        (C.clockAfter K n s)))

-- The canonical Nat-indexed orbit is an explicit infinite-state embedding:
-- equality of orbit states forces equality of the Nat indices.
canonicalInfiniteStateOrbitEmbedding :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState) →
  ∀ {m n : Nat} →
  C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
  m ≡ n
canonicalInfiniteStateOrbitEmbedding K s =
  canonicalOrbit-state-injective K s


canonicalPigeonholeNatClockContradiction :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → C.Int8)
  (inverse : C.Int8 → C.FullLearnerState) →
  (∀ t → inverse (observe t) ≡ t) →
  ⊥
canonicalPigeonholeNatClockContradiction K s observe inverse leftInverse =
  C.int8-no-countably-unbounded-injective
    (λ n → observe (C.iterateCanonical K n s))
    (λ {m} {n} eq →
      canonicalOrbit-state-injective K s
        (trans
          (sym (leftInverse (C.iterateCanonical K m s)))
          (trans
            (cong inverse eq)
            (leftInverse (C.iterateCanonical K n s)))))

------------------------------------------------------------------------
-- Full discrete exact-UAP factorization.
--
-- This is the genuine universal statement available without topology:
-- every target on the discrete state factors exactly through an observation
-- that has a left inverse. No limits, density arguments, or real-valued
-- approximation metric are involved.
------------------------------------------------------------------------

record DiscreteExactUAPTheorem
  (State Feature Output : Set)
  (observe : State → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor discreteExactUAPTheorem
  field
    leftInverse :
      ∀ s → inverse (observe s) ≡ s
    exactReadout :
      (target : State → Output) →
      ∀ s →
      target s ≡ target (inverse (observe s))

open DiscreteExactUAPTheorem public

------------------------------------------------------------------------
-- Full universal exact-discrete UAP, not merely one chosen target.
--
-- Universal exact readout means every target State → Output factors
-- exactly through the observation.  Constructively, this is equivalent
-- to existence of a left inverse.  The identity target supplies the
-- converse, so this result is independent of topology or approximation
-- metrics.
------------------------------------------------------------------------

record DiscreteLeftInverseWitness
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteLeftInverseWitness
  field
    inverse : Feature → State
    leftInverse :
      ∀ s → inverse (observe s) ≡ s

open DiscreteLeftInverseWitness public

record DiscreteExactUniversalUAP
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteExactUniversalUAP
  field
    readout :
      {Output : Set} →
      (State → Output) →
      Feature →
      Output
    exactReadout :
      {Output : Set} →
      (target : State → Output) →
      ∀ s →
      target s ≡ readout target (observe s)

open DiscreteExactUniversalUAP public

discreteExactUniversalUAP-from-leftInverse :
  ∀ {State Feature : Set}
  {observe : State → Feature} →
  DiscreteLeftInverseWitness State Feature observe →
  DiscreteExactUniversalUAP State Feature observe
discreteExactUniversalUAP-from-leftInverse witness =
  discreteExactUniversalUAP
    (λ target f → target (inverse witness f))
    (λ target s → cong target (leftInverse witness s))

discreteExactUniversalUAP-to-leftInverse :
  ∀ {State Feature : Set}
  {observe : State → Feature} →
  DiscreteExactUniversalUAP State Feature observe →
  DiscreteLeftInverseWitness State Feature observe
discreteExactUniversalUAP-to-leftInverse universal =
  discreteLeftInverseWitness
    (readout universal (λ s → s))
    (λ s → sym (exactReadout universal (λ t → t) s))

------------------------------------------------------------------------
-- Positive Nat-indexed exact-universal readout.
--
-- Nat supplies the countably infinite orbit index.  Exact universality still
-- comes from the left inverse; Nat cardinality only removes the finite-
-- codomain pigeonhole obstruction.
------------------------------------------------------------------------

canonicalNatIndexedExactUniversalReadout :
  ∀ {Feature Output : Set}
  (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ≡ t) →
  (target : C.FullLearnerState → Output) →
  ∀ n →
  target (C.iterateCanonical K n s) ≡
  target (inverse (observe (C.iterateCanonical K n s)))
canonicalNatIndexedExactUniversalReadout
  K s observe inverse leftInverse target n =
  cong
    target
    (sym (leftInverse (C.iterateCanonical K n s)))

record DiscreteExactUniversalUAPLeftInverseEquivalence
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteExactUniversalUAPLeftInverseEquivalence
  field
    fromLeftInverse :
      DiscreteLeftInverseWitness State Feature observe →
      DiscreteExactUniversalUAP State Feature observe
    toLeftInverse :
      DiscreteExactUniversalUAP State Feature observe →
      DiscreteLeftInverseWitness State Feature observe

discreteExactUniversalUAP-leftInverse-equivalence :
  ∀ {State Feature : Set}
  {observe : State → Feature} →
  DiscreteExactUniversalUAPLeftInverseEquivalence State Feature observe
discreteExactUniversalUAP-leftInverse-equivalence =
  discreteExactUniversalUAPLeftInverseEquivalence
    discreteExactUniversalUAP-from-leftInverse
    discreteExactUniversalUAP-to-leftInverse

