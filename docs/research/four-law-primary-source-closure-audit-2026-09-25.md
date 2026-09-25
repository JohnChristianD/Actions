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
- README.md
- docs/research/marl-laws-hodge-maxwell-f4-ray-2026-09-25.md
- .ci/discovery/current-semantic-emergence-2026-09-25.mmd

## Semantic-premise pruning update — 2026-09-25

The theorem monolith now distinguishes two levels that must not be conflated:

1. `NLabMaxwellSemanticClosure` is the physical semantic input. It contains the repository-facing Noether/current output and the variational/action output for the existing Hodge-Maxwell solution carrier.
2. `NLabMaxwellFourLawSemanticallyClosed` is a downstream proof-relevant package that also stores the learner kernel. Its consumers no longer restate the individual semantic premises.

The resulting closed-signature adapters are `nLabMaxwellFourLawOneStepClosed` and `nLabMaxwellIterateConjugacyClosed`. This is a genuine pruning of repeated conditionality at the theorem-consumer surface.

The pruning does not alter the existence boundary. The package still has to be inhabited by concrete current/trajectory compatibility and action/variation/stationarity semantics. The generic non-derivability result in `FourLawClosureImpossibility.agda` prevents a universal constructor from removing those mathematical obligations.

The Euler-Lagrange interface was also strengthened with the reverse implication from Euler-Lagrange shell to Maxwell shell, making the shell correspondence explicitly two-way rather than merely a one-way implication into stationarity.

## Literature resolution — 2026-09-25

The requested source expansion was checked against the exact Agda obligations rather than only the vocabulary.

### Maxwell / Noether

Wikipedia's Maxwell equations page records charge conservation as a corollary of the Maxwell system, while its differential-form presentation gives dF=0 and d⋆F=μ0J. The conserved-current page identifies the continuity equation as the local conservation statement. nLab's gauge-symmetry and geometry-of-physics material gives the corresponding Euler-Lagrange form for vacuum electromagnetism and the Noether identity obtained from commuting derivatives.

This supports the chain: Maxwell field equation + d² = 0 / commuting derivatives → local current conservation / Noether identity. But the repository Law-I contract asks for a stronger discrete trajectory equality. A continuum divergence-free current is not definitionally the same proposition as current(step p) ≡ current p.

Primary sources checked:
- https://ncatlab.org/nlab/show/A%2Bfirst%2Bidea%2Bof%2Bquantum%2Bfield%2B--%2BGauge%2Bsymmetries
- https://ncatlab.org/nlab/show/geometry%2Bof%2Bphysics%2B--%2Bperturbative%2Bquantum%2Bfield%2Btheory
- https://en.wikipedia.org/wiki/Maxwell%27s_equations
- https://en.wikipedia.org/wiki/Conserved_current

Itin's Noether currents and charges for Maxwell-like Lagrangians (arXiv:math-ph/0307003) reinforces the variational/current semantics but still does not define this repository's learner state or discrete step.

### Watanabe and Tsallis

The source chain does not provide the missing representation bridge. Tsallis's statistical-mechanics work treats entropy, probability distributions, and constrained variational/statistical principles; the Tsallis literature cites S. Watanabe's Knowing and Guessing in the information-theoretic background. Those results are relevant to Law IV's statistical semantics, not to the Law-I trajectory/current inverse or Law-III Maxwell action carrier in this repository.

Therefore no searched source supplies the missing concrete Agda inhabitant. Manufacturing one from a top-valued predicate, constant current, trivial action, or postulate would be semantic substitution rather than derivation.

### E-graph closure

The repository already contains the exact unconditional proof-only e-graph kernel in Exotic/ERL/FullCoupled/EGraphSemanticTransport.agda. Given an EGraphSemanticInterpretation with a sound interpretation, it proves reflexive, symmetric, and transitive semantic equality plus contextual and rewrite transport.

Thus the e-graph layer is no longer the physical bottleneck. The remaining physical frontier is exactly the inhabitance of NLabMaxwellSemanticClosure.

### Decision

1. Unconditional e-graph semantic closure: proved by the existing Agda transport kernel once semantic soundness is supplied.
2. Unconditional four-law physical closure: not derivable from the searched sources or current repository definitions without a concrete Law-I discrete current/trajectory compatibility theorem and concrete Law-III action/variation/stationarity data.

This is the strongest closure justified by the primary sources and the present type system.

## Knowledge-surface pruning — 2026-09-25

The obsolete branch-local wiki, the superseded nLab candidate note, and the unfinished Maxwell implementation plan are pruned from the maintained documentation surface. Their durable conclusions are retained here and in README.md: the typed Maxwell semantic boundary is proved as an adapter layer, while concrete Law-I current preservation and Law-III variational inhabitance remain separate physical obligations.

## 2026-09-25 expanded source pass

The expanded pass checked current authoritative pages across nLab, the Stanford Encyclopedia of Philosophy, Wikipedia, and tsallis.com.

### nLab

- Noether's theorem: continuous/variational symmetries yield conserved currents on the dynamical shell.
- Conserved current: a current is horizontally closed on the Euler-Lagrange shell; charges arise by integration over codimension-one slices.
- Maxwell's equations: the electromagnetic field/current equations are presented directly, including differential-form formulations.
- Hodge-Maxwell theorem: under its stated compact/oriented/Riemannian and exact-current hypotheses, a closed representative satisfying the inhomogeneous Maxwell equation exists uniquely in each cohomology class.
- Action functional / Euler-Lagrange equation: action critical loci encode physically realized configurations; Maxwell's equations are listed as an Euler-Lagrange example.

These sources support the semantic shape of the repository adapters. They do not supply the repository-specific discrete current-preservation equality, learner/solution inverse, or learner/physical step-conjugacy witnesses.

### Stanford Encyclopedia of Philosophy

The current Gauge Theories in Physics entry gives Maxwell's modern variables and equations, explicitly including conserved current, and explains the classical Lagrangian/Noether relation: Lagrangian symmetries yield conserved currents on solutions; the QED Euler-Lagrange equation produces the inhomogeneous Maxwell equation. This is an independent conceptual cross-check for the Noether and variational adapters.

### Wikipedia

The Maxwell equations entry records charge conservation as a consequence of Maxwell's equations. The electromagnetic tensor entry gives the field Euler-Lagrange route to the inhomogeneous Maxwell equation. The Euler-Lagrange and Noether entries provide the general variational/conservation background. These are cross-checks, not Agda proof sources.

### Tsallis / statistical-information boundary

tsallis.com describes Tsallis entropy as a one-parameter generalization of Boltzmann-Gibbs-Shannon entropy and emphasizes its nonadditive composition. Wikipedia's Tsallis entropy/statistics pages provide the q-logarithm/q-exponential and nonadditivity background. The repository's TsallisStatisticalRepresentation.agda remains deliberately carrier-polymorphic and arithmetic-free: it proves injectivity from an explicit decode-after-encode law rather than importing statistical literature as an axiom.

### Semantic conclusion

The expanded literature pass strengthens the semantic adapters but does not close the repository-specific physical existence boundary. The correct unconditional closure is:

supplied sound Agda semantic family → sound e-graph path → exact endpoint equality

with A* costs/heuristics used only for traversal. Physical Law-I/Law-III inhabitance remains an explicit typed input to NLabMaxwellSemanticClosure.


## 2026-09-25 semantic closure/index pass

The surviving Agda surface was read as a complete set rather than as a theorem-monolith sample:

- CanonicalLearnerMonolith.agda
- TheoremsMonolith.agda
- EGraphSemanticTransport.agda
- FourLawClosureWitnesses.agda
- FourLawClosureImpossibility.agda
- GRUStatisticalInjectivity.agda
- TsallisStatisticalRepresentation.agda
- RepositorySemanticEGraphClosure.agda

The repository semantic index now enumerates exactly these eight files. Its theorem is unconditional over the enumerated file, a supplied sound semantic interpretation, and a supplied sound e-graph path. A* contributes only cost/heuristic traversal metadata. Therefore the final semantic closure is an equality theorem over supplied semantics, not an existence theorem for every domain model.

The Maxwell semantic seam is also fully composed at the implication level: a supplied nLab-style conserved-current theorem plus a supplied Maxwell-shell proof yields the Law-I contract; a supplied Euler-Lagrange/Maxwell shell equivalence plus stationarity output yields the Law-III contract; the existing learner/solution inverse and step-conjugacy witness yields the physics-to-learner transition contract; these compose into the one-step four-law contract and arbitrary-horizon iterate conjugacy. The missing physical inhabitants themselves are not fabricated.

## Source-depth conclusion

The expanded source pass supports these distinctions. nLab explicitly defines conserved currents as horizontally closed on the dynamical shell and derives them from variational symmetries; its Maxwell and Hodge-Maxwell pages state the differential-form equations and the stated Hodge existence/uniqueness result. Its action-functional and Euler-Lagrange pages connect critical loci to equations of motion and list Maxwell's equations as an example.

SEP's gauge-theory discussion independently connects Maxwell/current conservation, classical Lagrangians, Noether's theorem, and Euler-Lagrange equations. Wikipedia cross-checks Maxwell charge conservation, the electromagnetic-tensor field equation, Noether conservation, and the Euler-Lagrange variational route. tsallis.com gives the current Tsallis entropy definition, nonadditivity, q-Gaussian construction, and current bibliography/news; Wikipedia's Tsallis pages add q-logarithm/q-exponential relations. None of those external sources defines this repository's discrete learner state, exact current/trajectory equality, or learner/Maxwell inverse. External sources therefore remain semantic evidence, never Agda proof inputs.

The placeholder citation marker above is intentionally not part of the repository's proof authority; the maintained source URLs and source-by-source findings remain in this audit's earlier sections.
