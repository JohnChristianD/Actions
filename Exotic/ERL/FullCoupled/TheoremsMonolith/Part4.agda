{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith.Part4 where

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

open import Exotic.ERL.FullCoupled.TheoremsMonolith.Part3 public

canonicalFiniteSampleExactUniversalReadout :
  ∀ {Feature Output : Set}
  (bound : Nat)
  (embed : Fin bound → C.FullLearnerState)
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.FullLearnerState Feature observe inverse)
  (target : C.FullLearnerState → Output)
  (i : Fin bound) →
  target (embed i) ≡ target (inverse (observe (embed i)))
canonicalFiniteSampleExactUniversalReadout
  bound embed observe inverse witness target i =
  continuousLeftInverse-exactReadout-transfer witness target (embed i)

------------------------------------------------------------------------
-- Ring-state injectivity and orbit-observation separation interfaces.
--
-- These are explicit theorem contracts. The strict import boundary does
-- not define a topology or an ordered-ring hierarchy, so neither is hidden.
------------------------------------------------------------------------

record OrbitStateInjectivityTheorem (State : Set) : Set₁ where
  constructor orbitStateInjectivityTheorem
  field
    orbitState : Nat → State
    orbitStateInjective :
      ∀ {m n} → orbitState m ≡ orbitState n → m ≡ n

open OrbitStateInjectivityTheorem public

canonicalOrbitStateInjective :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState) →
  OrbitStateInjectivityTheorem C.FullLearnerState
canonicalOrbitStateInjective K s =
  orbitStateInjectivityTheorem
    (λ n → C.iterateCanonical K n s)
    (λ {m} {n} eq → canonicalOrbit-state-injective K s eq)

record OrbitObservationSeparationTheorem
  (State Feature : Set)
  (embed : Nat → State)
  (observe : State → Feature) : Set₁ where
  constructor orbitObservationSeparationTheorem
  field
    observationSeparatesOrbitIndices :
      ∀ {m n} →
      observe (embed m) ≡ observe (embed n) →
      m ≡ n

open OrbitObservationSeparationTheorem public

canonicalOrbitObservationSeparation :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → C.Int8)
  (inverse : C.Int8 → C.FullLearnerState) →
  (∀ t → inverse (observe t) ≡ t) →
  OrbitObservationSeparationTheorem
    C.FullLearnerState
    C.Int8
    (λ n → C.iterateCanonical K n s)
    observe
canonicalOrbitObservationSeparation
  K s observe inverse leftInverse =
  orbitObservationSeparationTheorem
    (λ {m} {n} eq →
      canonicalOrbit-state-injective K s
        (trans
          (sym (leftInverse (C.iterateCanonical K m s)))
          (trans
            (cong inverse eq)
            (leftInverse (C.iterateCanonical K n s)))))

------------------------------------------------------------------------
-- Recurrent-prefix bounded exact UAP certificate.
--
-- The certificate makes the requested ingredients explicit:
-- recurrent depth/associative scan, orbit-observation separation,
-- a continuous left inverse, and Nat-indexed composition injectivity.
------------------------------------------------------------------------

record CanonicalRecurrentBoundedExactUniversalApproximationTheorem
  {Feature : Set}

  (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState) : Set₁ where
  constructor canonicalRecurrentBoundedExactUniversalApproximationTheorem
  field
    recurrentDepth :
      RecurrentAssociativeScanTheorem C.GRUState C.Int8

    continuousLeftInverse :
      ContinuousLeftInverseTheorem
        C.FullLearnerState
        Feature
        observe
        inverse

    natCompositionInjective :
      ∀ {m n : Nat} →
      C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
      m ≡ n

    observationSeparatesOrbitIndices :
      OrbitObservationSeparationTheorem
        C.FullLearnerState
        Feature
        (λ n → C.iterateCanonical K n s)
        observe

    boundedUniversalExactApproximation :
      ∀ {Output : Set} →
      ∀ (bound : Nat) →
      (target : C.FullLearnerState → Output) →
      (i : Fin bound) →
      target (C.iterateCanonical K (toℕ i) s) ≡
      target
        (inverse
          (observe
            (C.iterateCanonical K (toℕ i) s)))

open CanonicalRecurrentBoundedExactUniversalApproximationTheorem public

canonicalRecurrentBoundedExactUniversalApproximationTheorem-from-witness :
  ∀ {Feature : Set}

  (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.FullLearnerState
      Feature
      observe
      inverse) →
  CanonicalRecurrentBoundedExactUniversalApproximationTheorem
    K
    s
    observe
    inverse
canonicalRecurrentBoundedExactUniversalApproximationTheorem-from-witness
  K s observe inverse witness =
  canonicalRecurrentBoundedExactUniversalApproximationTheorem
    canonicalGRU-recurrent-associative-scan-theorem
    witness
    (canonicalInfiniteStateOrbitEmbedding K s)
    (orbitObservationSeparationTheorem
      (λ {m} {n} eq →
        canonicalOrbit-state-injective K s
          (trans
            (sym (leftInverse witness (C.iterateCanonical K m s)))
            (trans
              (cong inverse eq)
              (leftInverse witness (C.iterateCanonical K n s))))))
    (λ bound target i →
      continuousLeftInverse-exactReadout-transfer
        witness
        target
        (C.iterateCanonical K (toℕ i) s))

------------------------------------------------------------------------
-- Emergent finite-exact orbit/UAP composition theorem.
--
-- This composes theorem certificates only. It does not define a second
-- learner semantics: CanonicalLearnerMonolith remains the sole component
-- and transition semantics source.
------------------------------------------------------------------------

record CanonicalFiniteExactOrbitUAPCompositionTheorem : Set₁ where
  constructor canonicalFiniteExactOrbitUAPCompositionTheorem
  field
    aqLoop :
      CanonicalAQLoopTheorem

    hadamardAttentionRopePrefixComposition :
      CanonicalHadamardAttentionRopePrefixCompositionTheorem

    exactUniversalContinuousReadout :
      ∀ {Feature : Set}
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState)
      (witness :
        ContinuousLeftInverseTheorem
          C.FullLearnerState Feature observe inverse) →
      ExactUniversalApproximationThroughContinuousLeftInverse
        C.FullLearnerState Feature observe inverse

    boundedExactUniversalApproximation :
      ∀ {Feature : Set}
      (bound : Nat)
      (embed : Fin bound → C.FullLearnerState)
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState)
      (witness :
        ContinuousLeftInverseTheorem
          C.FullLearnerState Feature observe inverse) →
      BoundedContinuousLeftInverseExactApproximationTheorem
        C.FullLearnerState Feature observe inverse bound embed

    recurrentBoundedExactUniversalApproximation :
      ∀ {Feature : Set}
      (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState)
      (witness :
        ContinuousLeftInverseTheorem
          C.FullLearnerState Feature observe inverse) →
      CanonicalRecurrentBoundedExactUniversalApproximationTheorem
        K s observe inverse

    infiniteStateOrbit :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState) →
      ∀ {m n : Nat} →
      C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
      m ≡ n

    observationInjectivityFromLeftInverse :
      ∀ {Feature : Set}
      {observe : C.FullLearnerState → Feature}
      {inverse : Feature → C.FullLearnerState} →
      (leftInverse : ∀ t → inverse (observe t) ≡ t) →
      ∀ {x y} →
      observe x ≡ observe y →
      x ≡ y

    finiteFeatureCapacityContradiction :
      ∀ {Feature : Set}
      (bound : Nat)
      (encode : Feature → Fin bound)
      (encodeInjective :
        ∀ {x y} → encode x ≡ encode y → x ≡ y)
      (orbit : Nat → Feature)
      (orbitInjective :
        ∀ {m n} → orbit m ≡ orbit n → m ≡ n) →
      ⊥

    finiteInt8ContinuousLeftInverseContradiction :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → C.Int8)
      (inverse : C.Int8 → C.FullLearnerState) →
      Continuous
        C.FullLearnerState C.Int8
        (discreteTopology C.FullLearnerState)
        (discreteTopology C.Int8) observe →
      Continuous
        C.Int8 C.FullLearnerState
        (discreteTopology C.Int8)
        (discreteTopology C.FullLearnerState) inverse →
      (∀ t → inverse (observe t) ≡ t) →
      ⊥

    finiteTimeExactReadout :
      ∀ {Feature Output : Set}
      (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState) →
      (leftInverse : ∀ t → inverse (observe t) ≡ t) →
      (target : C.FullLearnerState → Output) →
      (horizon n : Nat) →
      n ≤ horizon →
      target (C.iterateCanonical K n s) ≡
      target (inverse (observe (C.iterateCanonical K n s)))

    finiteSampleExactReadout :
      ∀ {Feature Output : Set}
      (bound : Nat)
      (embed : Fin bound → C.FullLearnerState)
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState)
      (witness :
        ContinuousLeftInverseTheorem
          C.FullLearnerState Feature observe inverse)
      (target : C.FullLearnerState → Output)
      (i : Fin bound) →
      target (embed i) ≡ target (inverse (observe (embed i)))

    exactIterateComposition :
      ∀ (K : C.FullLearnerKernel)
      (m n : Nat)
      (s : C.FullLearnerState) →
      C.iterateCanonical K (m + n) s ≡
      C.iterateCanonical K n
        (C.iterateCanonical K m s)

    aperiodicity :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (n : Nat) →
      C.iterateCanonical K (suc n) s ≢ s

    finiteCycleExclusion :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (n : Nat) →
      C.iterateCanonical K (suc n) s ≡ s → ⊥

    finiteStateActionVisitCapacity :
      ∀ (stateCount actionCount : Nat)
      (visitCode : Nat → Fin (stateCount * actionCount)) →
      ¬ (∀ {m n} → visitCode m ≡ visitCode n → m ≡ n)

    noGlobalInt8DiscreteUAP :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → C.Int8)
      (inverse : C.Int8 → C.FullLearnerState)
      {Output : Set} →
      DiscreteExactUAPTheorem
        C.FullLearnerState C.Int8 Output observe inverse →
      ⊥

open CanonicalFiniteExactOrbitUAPCompositionTheorem public

canonical-finite-exact-orbit-uap-composition-theorem :
  CanonicalFiniteExactOrbitUAPCompositionTheorem
canonical-finite-exact-orbit-uap-composition-theorem =
  canonicalFiniteExactOrbitUAPCompositionTheorem
    canonical-aq-loop-theorem
    canonical-hadamard-attention-rope-prefix-composition-theorem
    (λ observe inverse witness →
      exactUniversalApproximationThroughContinuousLeftInverse-from-witness
        witness)
    boundedUniversalExactApproximation-through-continuousLeftInverse
    (λ K s observe inverse witness →
      canonicalRecurrentBoundedExactUniversalApproximationTheorem-from-witness
        K s observe inverse witness)
    canonicalInfiniteStateOrbitEmbedding
    leftInverse-observation-injective
    finiteFeatureCode-no-Nat-injective
    (λ K s observe inverse observeContinuous inverseContinuous leftInverse →
      canonicalNoGlobalInt8ContinuousLeftInverseOnDiscreteTopologies
        K s observe inverse observeContinuous inverseContinuous leftInverse)
    canonicalFiniteTimeExactUniversalReadout
    canonicalFiniteSampleExactUniversalReadout
    canonicalIterateComposition
    canonicalAperiodic-theorem
    canonicalNoNontrivialFiniteCycle-theorem
    finiteStateActionVisitInjectionImpossible
    canonicalNoGlobalInt8DiscreteUAPOnOrbit

------------------------------------------------------------------------
-- Strictly stronger combined theorem schema.
--
-- This is not a topological universal-approximation theorem under the
-- current imports. It is the exact composition available here:
-- target semantics + minimax/Bellman-Shapley inclusion + endogenous
-- left-inverse factorization + continuous-left-inverse transfer +
-- bounded exact approximation from the continuous left inverse + ring-state
-- injectivity + orbit-observation separation + Nat-clock pigeonhole
-- contradiction.
------------------------------------------------------------------------

record CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem : Set₁ where
  constructor canonicalEndogenousMinimaxBellmanShapleyUAPTheorem
  field
    exactUniversalObservationInjectivity :
      ∀ {Feature : Set}
      {observe : C.FullLearnerState → Feature}
      {inverse : Feature → C.FullLearnerState} →
      (leftInverse : ∀ s → inverse (observe s) ≡ s) →
      ∀ {s t} → observe s ≡ observe t → s ≡ t

    finiteFeatureInjectivityObstruction :
      ∀ {Feature : Set}
      (bound : Nat)
      (encode : Feature → Fin bound)
      (encodeInjective :
        ∀ {x y} → encode x ≡ encode y → x ≡ y)
      (orbit : Nat → Feature)
      (orbitInjective :
        ∀ {m n} → orbit m ≡ orbit n → m ≡ n) →
      ⊥

    finiteFeatureContinuousLeftInverseContradiction :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      {Feature : Set}
      (bound : Nat)
      (encode : Feature → Fin bound)
      (encodeInjective :
        ∀ {x y} → encode x ≡ encode y → x ≡ y)
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState) →
      Continuous
        C.FullLearnerState Feature
        (discreteTopology C.FullLearnerState)
        (discreteTopology Feature) observe →
      Continuous
        Feature C.FullLearnerState
        (discreteTopology Feature)
        (discreteTopology C.FullLearnerState) inverse →
      (∀ t → inverse (observe t) ≡ t) →
      ⊥

    finiteTimeExactReadout :
      ∀ {Feature Output : Set}
      (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState) →
      (leftInverse : ∀ t → inverse (observe t) ≡ t) →
      (target : C.FullLearnerState → Output) →
      (horizon n : Nat) →
      n ≤ horizon →
      target (C.iterateCanonical K n s) ≡
      target (inverse (observe (C.iterateCanonical K n s)))

    finiteSampleExactReadout :
      ∀ {Feature Output : Set}
      (bound : Nat)
      (embed : Fin bound → C.FullLearnerState)
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState)
      (witness : ContinuousLeftInverseTheorem
        C.FullLearnerState Feature observe inverse)
      (target : C.FullLearnerState → Output)
      (i : Fin bound) →
      target (embed i) ≡ target (inverse (observe (embed i)))

    iterateComposition :
      ∀ (K : C.FullLearnerKernel) (m n : Nat)
      (s : C.FullLearnerState) →
      C.iterateCanonical K (m + n) s ≡
      C.iterateCanonical K n (C.iterateCanonical K m s)

    hadamardAttentionRopePrefixComposition :
      CanonicalHadamardAttentionRopePrefixCompositionTheorem

    aperiodicity :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (n : Nat) →
      C.iterateCanonical K (suc n) s ≢ s

    finiteCycleExclusion :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (n : Nat) →
      C.iterateCanonical K (suc n) s ≡ s → ⊥

    finiteExactOrbitUAPComposition :
      CanonicalFiniteExactOrbitUAPCompositionTheorem

    finiteStateActionVisitInjectionCapacityTheorem :
      ∀ (stateCount actionCount : Nat)
      (visitCode : Nat → Fin (stateCount * actionCount)) →
      ¬ (∀ {m n} → visitCode m ≡ visitCode n → m ≡ n)

    targetSemantics :
      CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem

    exactDiscreteUAP :
      ∀ {Feature Output : Set}
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState) →
      (leftInverse : ∀ s → inverse (observe s) ≡ s) →
      DiscreteExactUAPTheorem
        C.FullLearnerState
        Feature
        Output
        observe
        inverse

    exactUniversalContinuousReadout :
      ∀ {Feature : Set}
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState)
      (witness :
        ContinuousLeftInverseTheorem
          C.FullLearnerState
          Feature
          observe
          inverse) →
      ExactUniversalApproximationThroughContinuousLeftInverse
        C.FullLearnerState
        Feature
        observe
        inverse

    inclusionClass :
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

    endogenousFactorization :
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
              (C.critic (C.watkins (inverse (observe s))))))
        (C.canonicalEndogenousFeedback K (inverse (observe s))))

    targetScan :
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


    continuousReadoutTransfer :
      ∀ {Feature Output : Set}
      {observe : C.FullLearnerState → Feature}
      {inverse : Feature → C.FullLearnerState} →
      ContinuousLeftInverseTheorem
        C.FullLearnerState
        Feature
        observe
        inverse →
      (target : C.FullLearnerState → Output) →
      ∀ s →
      target s ≡ target (inverse (observe s))

    boundedExactApproximation :
      ∀ {Feature : Set}

      (bound : Nat)
      (embed : Fin bound → C.FullLearnerState)
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState)
      (witness :
        ContinuousLeftInverseTheorem
          C.FullLearnerState
          Feature
          observe
          inverse) →
      BoundedContinuousLeftInverseExactApproximationTheorem
        C.FullLearnerState
        Feature
        observe
        inverse
        bound
        embed

    recurrentBoundedExactUniversalApproximation :
      ∀ {Feature : Set}

      (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → Feature)
      (inverse : Feature → C.FullLearnerState)
      (witness :
        ContinuousLeftInverseTheorem
          C.FullLearnerState
          Feature
          observe
          inverse) →
      CanonicalRecurrentBoundedExactUniversalApproximationTheorem
        K
        s
        observe
        inverse

    orbitStateInjection :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState) →
      OrbitStateInjectivityTheorem C.FullLearnerState

    infiniteStateOrbit :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState) →
      ∀ {m n : Nat} →
      C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
      m ≡ n

    observationSeparatesOrbitIndices :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → C.Int8)
      (inverse : C.Int8 → C.FullLearnerState) →
      (∀ t → inverse (observe t) ≡ t) →
      OrbitObservationSeparationTheorem
        C.FullLearnerState
        C.Int8
        (λ n → C.iterateCanonical K n s)
        observe

    pigeonholeNatClockContradiction :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → C.Int8)
      (inverse : C.Int8 → C.FullLearnerState) →
      (∀ t → inverse (observe t) ≡ t) →
      ⊥

    finiteInt8ContinuousLeftInverseContradiction :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → C.Int8)
      (inverse : C.Int8 → C.FullLearnerState) →
      (observeContinuous :
        Continuous
          C.FullLearnerState
          C.Int8
          (discreteTopology C.FullLearnerState)
          (discreteTopology C.Int8)
          observe) →
      (inverseContinuous :
        Continuous
          C.Int8
          C.FullLearnerState
          (discreteTopology C.Int8)
          (discreteTopology C.FullLearnerState)
          inverse) →
      (leftInverse : ∀ t → inverse (observe t) ≡ t) →
      ⊥

    noGlobalInt8DiscreteUAP :
      ∀ (K : C.FullLearnerKernel)
      (s : C.FullLearnerState)
      (observe : C.FullLearnerState → C.Int8)
      (inverse : C.Int8 → C.FullLearnerState)
      {Output : Set} →
      DiscreteExactUAPTheorem
        C.FullLearnerState
        C.Int8
        Output
        observe
        inverse →
      ⊥

canonical-endogenous-minimax-bellman-shapley-uap-theorem : CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem
canonical-endogenous-minimax-bellman-shapley-uap-theorem =
  canonicalEndogenousMinimaxBellmanShapleyUAPTheorem
    canonical-biased-watkins-negative-q-munchausen-l2-target-theorem
    canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class
    (λ observe inverse leftInverse →
      discreteExactUAPTheorem-from-leftInverse
        observe
        inverse
        leftInverse)
    (λ observe inverse witness →
      exactUniversalApproximationThroughContinuousLeftInverse-from-witness
        witness)
    (λ K observe inverse leftInverse s →
      canonicalWatkinsTarget-endogenous-leftInverse
        K observe inverse leftInverse s)
    (λ K s n h →
      canonicalWatkinsTarget-recurrent-prefix-correct
        K s n h)
    canonical-hadamard-attention-rope-prefix-composition-theorem
    (λ witness target s →
      continuousLeftInverse-exactReadout-transfer
        witness
        target
        s)
    boundedUniversalExactApproximation-through-continuousLeftInverse
    (λ K s observe inverse witness →
      canonicalRecurrentBoundedExactUniversalApproximationTheorem-from-witness
        K s observe inverse witness)
    canonicalOrbitStateInjective
    canonicalInfiniteStateOrbitEmbedding
    canonicalOrbitObservationSeparation
    canonicalPigeonholeNatClockContradiction
    (λ K s observe inverse observeContinuous inverseContinuous leftInverse →
      canonicalNoGlobalInt8ContinuousLeftInverseOnDiscreteTopologies
        K s observe inverse observeContinuous inverseContinuous leftInverse)
    canonicalNoGlobalInt8DiscreteUAPOnOrbit
    leftInverse-observation-injective
    finiteFeatureCode-no-Nat-injective
    canonicalNoGlobalFiniteFeatureContinuousLeftInverseOnDiscreteTopologies
    canonicalFiniteTimeExactUniversalReadout
    canonicalFiniteSampleExactUniversalReadout
    canonicalIterateComposition
    canonicalAperiodic-theorem
    canonicalNoNontrivialFiniteCycle-theorem
    canonical-finite-exact-orbit-uap-composition-theorem
    finiteStateActionVisitInjectionImpossible
