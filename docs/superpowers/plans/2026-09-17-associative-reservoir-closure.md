# Associative Reservoir Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use the superpowers TDD workflow task-by-task. Direct commits to `main`; no pull request.

**Goal:** Add finite recurrent-core periodicity, symmetric associative coupling, a genuine Nat-valued Lyapunov basin theorem, multiple contextual attractors, and an explicit reservoir-computing condition boundary without claiming real-valued UAT.

**Architecture:** Keep the clocked learner state separate from a finite standalone reservoir core. The clock proves the full learner is non-periodic; the finite core can recur. Add symmetric coupling and a Lyapunov energy certificate as separate layers, then expose neighborhood-separation/readout as an analytic interface requiring a later real/topological bridge.

**Tech Stack:** Agda 2.8.0, stdlib 2.4, `--safe`, `GeneralFullCoupledTheoremsMonolith.agda`, GitHub Actions.

## Constraints

- Preserve `referenceReturn`; keep regret out.
- Do not replace the canonical Möbius/rational activation with identity.
- In the canonical learner, `mobiusActivation8` is actually fed into `gruStep`; in the generalized learner, `FiniteRational` is currently a handwritten carrier and `rationalCode` drops its denominator before the GRU update.
- Keep new theorem surfaces in `GeneralFullCoupledTheoremsMonolith.agda`.
- No standard real-valued reservoir universality claim until topology, input/filter class, readout class, and approximation norm are formalized.

## Task 1: RED regression

**Files:** create `Exotic/ERL/FullCoupled/ReservoirAttractorTheorems_test.agda`; modify `.github/workflows/agda.yml`.

Add a test referencing not-yet-defined names:

```agda
{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ReservoirAttractorTheorems_test where
open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T
open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
finite-core-cycle : ∀ (R : L.Int8 → L.Int8) (s : L.Int8) → T.FiniteOrbitEventuallyPeriodic R s
finite-core-cycle = T.int8-orbit-eventually-periodic
```

Add an Agda CI step for this file. Commit the intentionally red gate first and record the failure.

## Task 2: finite core and clocked exclusion

**File:** `Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda`.

Add `Data.Nat.Induction.<-wellFounded`, `Induction.WellFounded.Acc`, and finite-state support as needed. Define:

```agda
record FiniteOrbitEventuallyPeriodic (S : Set) (step : S → S) (s : S) : Set where
  constructor finiteOrbitEventuallyPeriodic
  field
    preperiod : Nat
    period : Nat
    positivePeriod : period ≢ zero
    repeatLaw : iterateGeneric step (preperiod + period) s ≡ iterateGeneric step preperiod s
```

Prove `int8-orbit-eventually-periodic` by transporting `Int8` through `Fin 256` and using finite pigeonhole machinery. Add `learnerNoPeriodicOrbit` from `iterateLearner-clock`, not merely the current fixed-point theorem.

Add a conditional projection witness:

```agda
record ReservoirProjectionWitness (X S : Set) : Set₁ where
  constructor reservoirProjectionWitness
  field
    projectState : X → S
    projectedStep : S → S
    sourceStep : X → X
    commute : ∀ x → projectState (sourceStep x) ≡ projectedStep (projectState x)
```

Do not assert that the current full learner automatically commutes with a GRU-only projection.

## Task 3: associative attractors

**File:** same theorem monolith, plus extend the regression test.

Add:

```agda
record SymmetricCoupling (S C : Set) : Set₁ where
  constructor symmetricCoupling
  field
    coefficient : S → S → C
    couplingSymmetry : ∀ i j → coefficient i j ≡ coefficient j i

record BasinWitness {S : Set} (step : S → S) (A : S → Set) (s : S) : Set where
  constructor basinWitness
  field
    steps : Nat
    hits : A (iterateGeneric step steps s)

record AttractorLyapunovCertificate (S : Set) : Set₁ where
  constructor attractorLyapunovCertificate
  field
    step : S → S
    attractor : S → Set
    energy : S → Nat
    decidableAttractor : ∀ s → attractor s ⊎ ¬ attractor s
    invariant : ∀ s → attractor s → attractor (step s)
    outsideDecrease : ∀ s → ¬ attractor s → energy (step s) < energy s
```

Prove `lyapunov-basin` using `Nat` well-founded descent. Then add a multiple-attractor record exposing pairwise disjointness, invariance, cue/basin selection, and contextual recall. Add a minimal static-readout witness and an explicitly labeled neighborhood-separation witness as an analytic boundary, not a fake finite-topology theorem.

## Task 4: Möbius boundary clarity

Preserve the canonical path and add explicit theorems for the canonical `mobiusActivation8` boundary and `f(0)=0`. Record that generalized `rationalCode` projects a rational to its numerator carrier. Do not call the generalized `gruStep` literally rational-valued until the denominator participates in the transition.

## Task 5: GREEN and completion evidence

Run the new regression, generalized learner, theorem monolith, canonical learner, benchmark, and Haskell/Cabal gates in CI. Verify no `.py`, `.sh`, `evosax`, or `RandomSearch` legacy harnesses reappear. Verify `main` and no PR. Report each result as proven, literature-supported, interface-only, or not established.
