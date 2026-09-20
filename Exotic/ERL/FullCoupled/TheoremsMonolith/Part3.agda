{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith.Part3 where

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

open import Exotic.ERL.FullCoupled.TheoremsMonolith.Part2 public

discreteLeftInverse-observe-injective :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State} →
  (∀ s → inverse (observe s) ≡ s) →
  ∀ {s t} →
  observe s ≡ observe t →
  s ≡ t
discreteLeftInverse-observe-injective leftInverse {s} {t} eq =
  trans
    (sym (leftInverse s))
    (trans
      (cong inverse eq)
      (leftInverse t))

discreteExactUAPTheorem-from-leftInverse :
  ∀ {State Feature Output : Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (leftInverse : ∀ s → inverse (observe s) ≡ s) →
  DiscreteExactUAPTheorem State Feature Output observe inverse
discreteExactUAPTheorem-from-leftInverse
  observe inverse leftInverse =
  discreteExactUAPTheorem
    leftInverse
    (λ target s → cong target (sym (leftInverse s)))

------------------------------------------------------------------------
-- Exact recurrent scan of the executable endogenous target stream.
canonicalNoGlobalInt8DiscreteUAPOnOrbit :
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
canonicalNoGlobalInt8DiscreteUAPOnOrbit
  K s observe inverse witness =
  canonicalPigeonholeNatClockContradiction
    K
    s
    observe
    inverse
    (leftInverse witness)

------------------------------------------------------------------------
-- Finite-observation contradiction even after granting continuity.
--
-- The discrete topologies make continuity automatic.  The contradiction
-- therefore comes strictly from the infinite canonical orbit versus the
-- finite Int8 observation space, not from a continuity failure.
------------------------------------------------------------------------

canonicalNoGlobalInt8ContinuousLeftInverseOnDiscreteTopologies :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → C.Int8)
  (inverse : C.Int8 → C.FullLearnerState) →
  Continuous
    C.FullLearnerState
    C.Int8
    (discreteTopology C.FullLearnerState)
    (discreteTopology C.Int8)
    observe →
  Continuous
    C.Int8
    C.FullLearnerState
    (discreteTopology C.Int8)
    (discreteTopology C.FullLearnerState)
    inverse →
  (∀ t → inverse (observe t) ≡ t) →
  ⊥
canonicalNoGlobalInt8ContinuousLeftInverseOnDiscreteTopologies
  K s observe inverse _ _ leftInverse =
  canonicalPigeonholeNatClockContradiction
    K
    s
    observe
    inverse
    leftInverse

canonicalNoGlobalInt8DiscreteUniversalUAPOnOrbit :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  (observe : C.FullLearnerState → C.Int8) →
  DiscreteExactUniversalUAP
    C.FullLearnerState
    C.Int8
    observe →
  ⊥
canonicalNoGlobalInt8DiscreteUniversalUAPOnOrbit
  K s observe universal =
  let
    witness = discreteExactUniversalUAP-to-leftInverse universal
  in
  canonicalPigeonholeNatClockContradiction
    K
    s
    observe
    (inverse witness)
    (leftInverse witness)

------------------------------------------------------------------------
-- Continuous left-inverse transfer.
--
-- The strict import boundary does not contain topology. Continuity is
-- therefore an explicit predicate supplied by the theorem caller.
------------------------------------------------------------------------

record ContinuousLeftInverseTheorem
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor continuousLeftInverseTheorem
  field
    stateTopology : Topology State
    featureTopology : Topology Feature
    observeContinuous : Continuous State Feature stateTopology featureTopology observe
    inverseContinuous : Continuous Feature State featureTopology stateTopology inverse
    leftInverse :
      ∀ s → inverse (observe s) ≡ s

open ContinuousLeftInverseTheorem public

continuousLeftInverse-injective :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State}

  ContinuousLeftInverseTheorem
    State Feature observe inverse →
  ∀ {s t} →
  observe s ≡ observe t →
  s ≡ t
continuousLeftInverse-injective witness {s} {t} eq =
  trans
    (sym (leftInverse witness s))
    (trans
      (cong inverse eq)
      (leftInverse witness t))

continuousLeftInverse-exactReadout-transfer :
  ∀ {State Feature Output : Set}
  {observe : State → Feature}
  {inverse : Feature → State}

  ContinuousLeftInverseTheorem
    State Feature observe inverse →
  (target : State → Output) →
  ∀ s →
  target s ≡ target (inverse (observe s))
continuousLeftInverse-exactReadout-transfer
  witness target s =
  cong target (sym (leftInverse witness s))

------------------------------------------------------------------------
-- Generic injectivity/capacity consequences.
------------------------------------------------------------------------

leftInverse-observation-injective :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State} →
  (leftInverse : ∀ s → inverse (observe s) ≡ s) →
  ∀ {s t} →
  observe s ≡ observe t →
  s ≡ t
leftInverse-observation-injective leftInverse eq =
  trans
    (sym (leftInverse _))
    (trans
      (cong _ eq)
      (leftInverse _))

discreteExactUniversalUAP-observation-injective :
  ∀ {State Feature : Set}
  {observe : State → Feature} →
  DiscreteExactUniversalUAP State Feature observe →
  ∀ {s t} →
  observe s ≡ observe t →
  s ≡ t
discreteExactUniversalUAP-observation-injective universal =
  let witness = discreteExactUniversalUAP-to-leftInverse universal
  in
  leftInverse-observation-injective (leftInverse witness)

canonicalLeftInverse-orbit-injective :
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState)
  {Feature : Set}
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ≡ t) →
  ∀ {m n} →
  observe (C.iterateCanonical K m s) ≡
  observe (C.iterateCanonical K n s) →
  m ≡ n
canonicalLeftInverse-orbit-injective
  K s observe inverse leftInverse eq =
  canonicalOrbit-state-injective K s
    (leftInverse-observation-injective leftInverse eq)

finiteFeatureCode-no-Nat-injective :
  ∀ {Feature : Set}
  (bound : Nat)
  (encode : Feature → Fin bound)
  (encodeInjective :
    ∀ {x y} → encode x ≡ encode y → x ≡ y)
  (orbit : Nat → Feature)
  (orbitInjective :
    ∀ {m n} → orbit m ≡ orbit n → m ≡ n) →
  ⊥
finiteFeatureCode-no-Nat-injective
  bound encode encodeInjective orbit orbitInjective =
  ℕ→Fin-notInjective
    (λ n → encode (orbit n))
    (λ {m} {n} eq →
      orbitInjective (encodeInjective eq))

canonicalNoGlobalFiniteFeatureContinuousLeftInverseOnDiscreteTopologies :
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
canonicalNoGlobalFiniteFeatureContinuousLeftInverseOnDiscreteTopologies
  K s bound encode encodeInjective observe inverse _ _ leftInverse =
  finiteFeatureCode-no-Nat-injective
    bound encode encodeInjective
    (λ n → observe (C.iterateCanonical K n s))
    (canonicalLeftInverse-orbit-injective K s observe inverse leftInverse)

------------------------------------------------------------------------
-- Finite state/action visit capacity.
------------------------------------------------------------------------

finiteStateActionVisitInjectionImpossible :
  ∀ (stateCount actionCount : Nat)
  (visitCode : Nat → Fin (stateCount * actionCount)) →
  ¬ (∀ {m n} → visitCode m ≡ visitCode n → m ≡ n)
finiteStateActionVisitInjectionImpossible stateCount actionCount visitCode =
  ℕ→Fin-notInjective visitCode

------------------------------------------------------------------------
-- Canonical Watkins exact AUP/UAP factorization through a continuous
-- left-invertible observation.  The result is exact equality, not a
-- metric approximation claim.
------------------------------------------------------------------------

canonicalWatkinsTarget-exactReadout-through-continuousLeftInverse :
  ∀ {Feature : Set}

  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.FullLearnerState
      Feature
      observe
      inverse) →
  ∀ (K : C.FullLearnerKernel)
  (s : C.FullLearnerState) →
  C.canonicalWatkinsTarget K s ≡
  C.canonicalWatkinsTarget K (inverse (observe s))
canonicalWatkinsTarget-exactReadout-through-continuousLeftInverse
  observe inverse witness K s =
  continuousLeftInverse-exactReadout-transfer
    witness
    (C.canonicalWatkinsTarget K)
    s

canonicalWatkinsTarget-boundedUniversalExactAUP :
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
  ∀ (K : C.FullLearnerKernel)
  (i : Fin bound) →
  C.canonicalWatkinsTarget K (embed i) ≡
  C.canonicalWatkinsTarget K (inverse (observe (embed i)))
canonicalWatkinsTarget-boundedUniversalExactAUP
  bound embed observe inverse witness K i =
  canonicalWatkinsTarget-exactReadout-through-continuousLeftInverse
    observe
    inverse
    witness
    K
    (embed i)

------------------------------------------------------------------------
-- Explicit finite-time exact universal readout.
------------------------------------------------------------------------

canonicalFiniteTimeExactUniversalReadout :
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
canonicalFiniteTimeExactUniversalReadout
  K s observe inverse leftInverse target _ n _ =
  canonicalNatIndexedExactUniversalReadout K s observe inverse leftInverse target n

------------------------------------------------------------------------
-- Bounded exact approximation/readout.
--
-- The domain is finite by construction: it is indexed by Fin bound.
-- Exact equality is the approximation relation, so no metric, limit,
-- compactness, or infinite orbit is required.  The only semantic input
-- beyond the finite index is a continuous left inverse.
------------------------------------------------------------------------

record BoundedContinuousLeftInverseExactApproximationTheorem
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State)

  (bound : Nat)
  (embed : Fin bound → State) : Set₁ where
  constructor boundedContinuousLeftInverseExactApproximationTheorem
  field
    continuousLeftInverseWitness :
      ContinuousLeftInverseTheorem
        State
        Feature
        observe
        inverse

    exactReadoutOnBound :
      {Output : Set} →
      (target : State → Output) →
      (i : Fin bound) →
      target (embed i) ≡
      target (inverse (observe (embed i)))

    observationInjectiveOnBound :
      ∀ {i j : Fin bound} →
      observe (embed i) ≡ observe (embed j) →
      embed i ≡ embed j

open BoundedContinuousLeftInverseExactApproximationTheorem public
------------------------------------------------------------------------
-- Standalone exact universal readout certificate.
--
-- This is the minimal universal form: a continuous left inverse gives
-- exact factorization of every target through the observation, while
-- separation is exposed explicitly as a derived contract.
------------------------------------------------------------------------

record ExactUniversalApproximationThroughContinuousLeftInverse
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor exactUniversalApproximationThroughContinuousLeftInverse
  field
    continuousLeftInverse :
      ContinuousLeftInverseTheorem
        State
        Feature
        observe
        inverse

    observationSeparation :
      ∀ {s t : State} →
      observe s ≡ observe t →
      s ≡ t

    exactUniversalReadout :
      ∀ {Output : Set} →
      (target : State → Output) →
      ∀ s →
      target s ≡ target (inverse (observe s))

open ExactUniversalApproximationThroughContinuousLeftInverse public

exactUniversalApproximationThroughContinuousLeftInverse-from-witness :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State} →
  ContinuousLeftInverseTheorem
    State
    Feature
    observe
    inverse →
  ExactUniversalApproximationThroughContinuousLeftInverse
    State
    Feature
    observe
    inverse
exactUniversalApproximationThroughContinuousLeftInverse-from-witness witness =
  exactUniversalApproximationThroughContinuousLeftInverse
    witness
    (continuousLeftInverse-injective witness)
    (λ target s →
      continuousLeftInverse-exactReadout-transfer
        witness
        target
        s)


boundedContinuousLeftInverseExactApproximationTheorem-from-witness :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State}

  (bound : Nat)
  (embed : Fin bound → State)
  (witness :
    ContinuousLeftInverseTheorem
      State
      Feature
      observe
      inverse) →
  BoundedContinuousLeftInverseExactApproximationTheorem
    State
    Feature
    observe
    inverse
    bound
    embed
boundedContinuousLeftInverseExactApproximationTheorem-from-witness
  bound embed witness =
  boundedContinuousLeftInverseExactApproximationTheorem
    witness
    (λ target i →
      continuousLeftInverse-exactReadout-transfer
        witness
        target
        (embed i))
    (λ {i} {j} eq →
      continuousLeftInverse-injective witness eq)

boundedExactApproximation-on-boundedOrbit :
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
boundedExactApproximation-on-boundedOrbit
  bound embed observe inverse witness =
  boundedContinuousLeftInverseExactApproximationTheorem-from-witness
    bound
    embed
    witness

-- Named universal form: every output target factors exactly through the
-- observation on the finite bound, provided the observation has a
-- continuous left inverse. "Approximation" is exact equality here.
boundedUniversalExactApproximation-through-continuousLeftInverse :
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
boundedUniversalExactApproximation-through-continuousLeftInverse
  bound embed observe inverse witness =
  boundedExactApproximation-on-boundedOrbit
    bound
    embed
    observe
    inverse
    witness


------------------------------------------------------------------------
-- Additional bounded exact UAP corollaries.
------------------------------------------------------------------------

boundedUniversalExactUAP-retraction :
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
      inverse)
  (i : Fin bound) →
  inverse (observe (embed i)) ≡ embed i
boundedUniversalExactUAP-retraction
  bound embed observe inverse witness i =
  leftInverse witness (embed i)

boundedUniversalExactUAP-decoder-transport :
  ∀ {Feature Output : Set}

  (bound : Nat)
  (embed : Fin bound → C.FullLearnerState)
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.FullLearnerState
      Feature
      observe
      inverse)
  (decoder : Feature → C.FullLearnerState)
  (decoderOnBound :
    ∀ i → decoder (observe (embed i)) ≡ inverse (observe (embed i)))
  (target : C.FullLearnerState → Output)
  (i : Fin bound) →
  target (embed i) ≡ target (decoder (observe (embed i)))
boundedUniversalExactUAP-decoder-transport
  bound embed observe inverse witness decoder decoderOnBound target i =
  trans
    (continuousLeftInverse-exactReadout-transfer
      witness
      target
      (embed i))
    (cong target (sym (decoderOnBound i)))

boundedUniversalExactUAP-postcompose :
  ∀ {Feature Output Output₂ : Set}

  (bound : Nat)
  (embed : Fin bound → C.FullLearnerState)
  (observe : C.FullLearnerState → Feature)
  (inverse : Feature → C.FullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.FullLearnerState
      Feature
      observe
      inverse)
  (target : C.FullLearnerState → Output)
  (post : Output → Output₂)
  (i : Fin bound) →
  post (target (embed i)) ≡
  post (target (inverse (observe (embed i))))
boundedUniversalExactUAP-postcompose
  bound embed observe inverse witness target post i =
  cong post
    (continuousLeftInverse-exactReadout-transfer
      witness
      target
      (embed i))

------------------------------------------------------------------------
-- Explicit finite-sample exact universal readout.
------------------------------------------------------------------------

