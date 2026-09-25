# Four-law primary-source closure audit — 2026-09-25

## Scope

This note tests whether standard variational, current, Hodge-Maxwell, and nonextensive-statistical formalisms supply the missing unconditional Law-I/Law-III/physics-to-learner witnesses already identified by the repository.

The external sources are used as semantic guidance only. They do not become Agda proof authority.

## Findings

### 1. Law III: variational / virtual-work structure is conditional on admissible variations and dynamics

The nLab presentation of Noether's theorem derives Euler-Lagrange equations from a stationary-action condition with boundary restrictions on the variation, and derives conserved currents from variational symmetries. The source therefore supports the repository's intended Law-III vocabulary—action, variation, equations of motion, conserved current—but it does not provide a universal inverse representation from an arbitrary learner state to a variational physical state.

Source: https://ncatlab.org/nlab/show/Noether%27s%2Btheorem

Wikipedia's virtual-work and Lagrangian-mechanics pages likewise formulate virtual work over admissible virtual displacements and derive dynamics from variational assumptions. The admissible-displacement/constraint data are part of the mathematical statement rather than consequences of the learner algebra.

Sources:
- https://en.wikipedia.org/wiki/Virtual_work
- https://en.wikipedia.org/wiki/Lagrangian_mechanics
- https://en.wikipedia.org/wiki/Hamilton%27s_principle

The Watanabe reference on Lagrange describes generalized coordinates, virtual work, constrained motion, and Euler-Lagrange equations. It is useful as a secondary exposition, but it is not treated as proof authority.

Source: https://watanabe.you/wiki/Joseph-Louis_Lagrange

**Closure consequence:** these sources tell us what a concrete Law-III witness must expose: a physical state/configuration carrier, admissible variation carrier, variational functional or equivalent force law, stationarity/virtual-work predicate, and an explicit representation map with inverse laws. They do not instantiate those objects in this repository.

### 2. Law I: particle trajectories and four-current require an actual trajectory/state map

The nLab Maxwell material identifies the electromagnetic source as a current form and gives the differential-form Maxwell equations d F = 0 and d * F = j. The electric-charge page also explains that d * F = j implies current conservation because d j = 0.

Sources:
- https://ncatlab.org/nlab/show/Maxwell%27s%2Bequations
- https://ncatlab.org/nlab/show/pre-metric%2Belectromagnetism
- https://ncatlab.org/nlab/show/electric%2Bcharge

This aligns with the repository's Law-I graph node for particle trajectories and particle four-current, but it does not define the missing particle worldline/state carrier or its inverse representation. Maxwell's current equation consumes a current; it does not manufacture a unique particle trajectory from an arbitrary learner state.

**Closure consequence:** a concrete Law-I witness must expose at least a particle/agent state carrier, trajectory/current construction, representation map, inverse law (or equivalent left/right inverse data), and compatibility of the physical transition with that representation.

### 3. Law II is already the repository's strongest exact bridge

The nLab Hodge-Maxwell theorem describes the same structural pattern used by the repository: a closed differential form plus a sourced Hodge-dual equation, with a unique representative under stated geometric/cohomological conditions.

Source: https://ncatlab.org/nlab/show/Hodge-Maxwell%2Btheorem

The repository already packages its Law-II carrier-polymorphic exact representation in ContinuousHodgeMaxwellExactRepresentationData and ConnectedContinuousHodgeMaxwellGRURepresentationTheorem. No new external axiom is needed here.

### 4. Tsallis entropy does not remove the representation gap

The official Tsallis site defines the q-entropy and its nonadditive composition law and presents q-Gaussian distributions as maximum-entropy distributions under stated constraints. Wikipedia likewise describes Tsallis entropy as a generalized entropy.

Sources:
- https://tsallis.com/
- https://en.wikipedia.org/wiki/Tsallis_entropy

This supports the repository's distinction between the canonical statistical/GRU layer and additional stochastic/spectral hypotheses. It does not provide a Law-I trajectory inverse, a Law-III variational inverse, or a physics-to-learner transition conjugacy.

In particular, introducing a q-entropy/q-distribution does not logically supply an encode/decode pair for the physical state. The constraint set, distribution family, state carrier, and transition semantics still have to be specified.

## Exact repository consequence

```text
Law-I trajectory/current witness
        +
Law-III admissible-variation / virtual-work witness
        +
physics -> learner transition conjugacy
        +
existing Law-II Hodge-Maxwell representation
        +
existing Law-IV GRU statistical representation
        |
        v
four-law one-step commuting square
        |
        v
n-step iterate conjugacy
        |
        v
prefix concatenation transport
        |
        v
exact prefix/horizon end-to-end closure
```

The first three inputs remain proof obligations in Agda. The external references do not justify replacing them with axioms or graph edges.

## Anti-shortcut decision

Do **not** add a theorem claiming unconditional four-law closure merely because stationary action, virtual work, Maxwell equations, or Tsallis entropy are standard physical/statistical principles. Each of those principles has explicit domains, constraints, admissibility conditions, or state semantics.

The correct next implementation seam is a minimal typed witness package whose fields correspond to the concrete definitions actually present in the repository. If those definitions do not exist, the honest next artifact is the interface record plus a blocked constructor—not an inhabited theorem.

## Transition-adapter update — 2026-09-25

The existing `CanonicalLearnerHodgeMaxwellCompositionTheorem` now has a direct Agda adapter, `canonical-physics-to-learner-transition-witness`, which packages its learner-to-solution inverse laws and `learnerStepConjugacy` into the repository's `PhysicsToLearnerTransitionWitness` contract. This removes duplication at the transition seam, but it does not manufacture the Law-I trajectory/current or Law-III admissibility/stationarity witnesses.

## Verification status

- External semantic audit completed against nLab, Watanabe, Tsallis, and Wikipedia.
- Repository search found no concrete virtualWork, Lagrangian, particle-trajectory, four-current, or Law-I/Law-III witness implementation on the current canonical branch.
- A proof-relevant physics-to-learner adapter was added from the existing Hodge-Maxwell/full-learner bridge.
- No unconditional four-law closure is claimed by this change.
- CI verification of the new Agda declaration is pending for the new branch.

## References to repository proof authority

- Exotic/ERL/FullCoupled/TheoremsMonolith.agda
- docs/wiki.md
- docs/research/marl-laws-hodge-maxwell-f4-ray-2026-09-25.md
- .ci/discovery/current-semantic-emergence-2026-09-25.mmd