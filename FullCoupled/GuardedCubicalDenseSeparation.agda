{-# OPTIONS --cubical #-}
{-# OPTIONS --guardedness #-}

module FullCoupled.GuardedCubicalDenseSeparation where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Cubical.Foundations.Prelude

------------------------------------------------------------------------
-- Guarded Cubical representation kernel.
--
-- The representation is an infinite guarded trace.  Cubical paths give
-- the equality notion; guarded coinduction supplies the unbounded
-- observation stream.  Density is explicit semantic data: the kernel
-- does not silently infer a topological density theorem from injectivity.
------------------------------------------------------------------------

record GuardedTrace (A : Set) : Set where
  coinductive
  field
    head : A
    tail : GuardedTrace A

open GuardedTrace public

traceStage :
  ∀ {A : Set} →
  Nat →
  GuardedTrace A →
  A
traceStage zero trace = head trace
traceStage (suc n) trace = traceStage n (tail trace)

record GuardedDenseRepresentation
  (State Feature : Set) : Set₁ where
  constructor guardedDenseRepresentation
  field
    observe :
      State →
      GuardedTrace Feature

    decode :
      GuardedTrace Feature →
      State

    leftInverse :
      ∀ s →
      decode (observe s) ≡ s

    denseSeparation :
      ∀ {s t} →
      s ≢ t →
      Σ Nat
        (λ n →
          traceStage n (observe s) ≢
          traceStage n (observe t))

open GuardedDenseRepresentation public

guardedGlobalInjective :
  ∀ {State Feature : Set} →
  (R : GuardedDenseRepresentation State Feature) →
  ∀ {s t} →
  observe R s ≡ observe R t →
  s ≡ t
guardedGlobalInjective R {s} {t} eq =
  sym (leftInverse R s)
  ∙ cong (decode R) eq
  ∙ leftInverse R t

guardedPointSeparation :
  ∀ {State Feature : Set} →
  (R : GuardedDenseRepresentation State Feature) →
  ∀ {s t} →
  s ≢ t →
  observe R s ≢ observe R t
guardedPointSeparation R neq collision =
  neq (guardedGlobalInjective R collision)

------------------------------------------------------------------------
-- Conjugacy over the guarded representation.
------------------------------------------------------------------------

iterate :
  ∀ {A : Set} →
  (A → A) →
  Nat →
  A →
  A
iterate step zero s = s
iterate step (suc n) s =
  iterate step n (step s)

record GuardedConjugacy
  (State Feature : Set)
  (stateStep : State → State)
  (featureStep : GuardedTrace Feature → GuardedTrace Feature)
  (R : GuardedDenseRepresentation State Feature) : Set₁ where
  constructor guardedConjugacy
  field
    stepConjugacy :
      ∀ s →
      observe R (stateStep s) ≡
      featureStep (observe R s)

open GuardedConjugacy public

guardedIterateConjugacy :
  ∀ {State Feature : Set}
  {stateStep : State → State}
  {featureStep : GuardedTrace Feature → GuardedTrace Feature}
  {R : GuardedDenseRepresentation State Feature}
  (C : GuardedConjugacy State Feature stateStep featureStep R) →
  ∀ n s →
  observe R (iterate stateStep n s) ≡
  iterate featureStep n (observe R s)
guardedIterateConjugacy C zero s = refl
guardedIterateConjugacy C (suc n) s =
  guardedIterateConjugacy C n (stateStep s)
  ∙ cong
      (iterate (featureStep))
      (stepConjugacy C s)

guardedOrbitInjectiveFromFeatureEquality :
  ∀ {State Feature : Set}
  {stateStep : State → State}
  {featureStep : GuardedTrace Feature → GuardedTrace Feature}
  {R : GuardedDenseRepresentation State Feature}
  (C : GuardedConjugacy State Feature stateStep featureStep R) →
  ∀ n {s t} →
  iterate featureStep n (observe R s) ≡
  iterate featureStep n (observe R t) →
  iterate stateStep n s ≡
  iterate stateStep n t
guardedOrbitInjectiveFromFeatureEquality C n {s} {t} eq =
  guardedGlobalInjective _
    (sym (guardedIterateConjugacy C n s)
     ∙ eq
     ∙ guardedIterateConjugacy C n t)

------------------------------------------------------------------------
-- Emergent composition seam.
--
-- An emergent theorem is an explicit witness supplied by the surrounding
-- development.  The guarded-Cubical kernel contributes path-level
-- injectivity, dense separation, and exact iterate conjugacy; it does not
-- invent the emergent witness.
------------------------------------------------------------------------

record GuardedDenseSeparationEmergentComposition
  (State Feature Emergent : Set)
  (stateStep : State → State)
  (featureStep : GuardedTrace Feature → GuardedTrace Feature)
  (R : GuardedDenseRepresentation State Feature)
  (C : GuardedConjugacy State Feature stateStep featureStep R) : Set₁ where
  constructor guardedDenseSeparationEmergentComposition
  field
    emergentWitness :
      Emergent

    globallyInjective :
      ∀ {s t} →
      observe R s ≡ observe R t →
      s ≡ t

    densePointSeparation :
      ∀ {s t} →
      s ≢ t →
      observe R s ≢ observe R t

    exactIterateConjugacy :
      ∀ n s →
      observe R (iterate stateStep n s) ≡
      iterate featureStep n (observe R s)

open GuardedDenseSeparationEmergentComposition public

guardedDenseSeparationEmergentComposition-from-witness :
  ∀ {State Feature Emergent : Set}
  {stateStep : State → State}
  {featureStep : GuardedTrace Feature → GuardedTrace Feature}
  {R : GuardedDenseRepresentation State Feature}
  {C : GuardedConjugacy State Feature stateStep featureStep R} →
  Emergent →
  GuardedDenseSeparationEmergentComposition
    State
    Feature
    Emergent
    stateStep
    featureStep
    R
    C
guardedDenseSeparationEmergentComposition-from-witness E =
  guardedDenseSeparationEmergentComposition
    E
    (guardedGlobalInjective _)
    (guardedPointSeparation _)
    (guardedIterateConjugacy _)
