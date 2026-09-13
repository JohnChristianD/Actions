# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

Repository CI authority: `.github/workflows/agda.yml`, which reads `.ci/canonical-module.txt` and checks both listed files with `agda --safe`.

Current manifest:

- `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

`AllSafeCombined.agda` is a regression bundle, not by itself the complete learner+EA theorem. `Agda/README.md` describes the larger v147 closure target; do not promote that target merely from documentation.

## Permanent arithmetic and theorem-scope exclusions

The repository is finite, dyadic, Int8-oriented, and kernel-checked. The CI gate rejects non-finite analytic theorem families and the excluded bootstrapping family before any Agda proof gate runs. The prohibition is structural: a forbidden family returning in source, documentation, generated candidates, or metadata fails CI.

No external theorem family may be imported as a proof shortcut. External references may be audited, but no external source can enlarge the accepted Agda theorem surface without a repository-local `--safe` proof.

## Canonical architecture

Intended canonical configuration:

- optimizer: `standardTDLambdaInt8`
- explorer: `modifiedDyadicMR15GA`
- precision: 8 bits
- context window power: 4
- frozen Haar feature
- local attention scale
- mutation target: independent finite dyadic draws per tick
- exact dyadic histogram fitness with exact sorting and rank consistency

The proof authority is the exact Agda definitions that are present in-tree and checked by `agda --safe`.

## Exploration theorem surface

The live exploration theorem comparison is explicitly three-method:

1. MR15: `Exotic/ERL/Exploration/MR15Reachability.agda`
2. OpenES: `Exotic/ERL/Exploration/OpenESDyadic.agda`
3. Noisy Nets: `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

The generic theorem layer is `Exotic/ERL/Exploration/ExplorationTheoremSchema.agda`.

The former pure DMCP distribution module is removed. It is not treated as a fourth exploration mechanism or as a canonical live probability layer.

### Exact finite probability ablations

`Exotic/ERL/Exploration/LazyWalkDyadic.agda` now gives a fully constructive lazy-walk mass law with common denominator 4: stay has numerator 2, forward has numerator 1, and backward has numerator 1. The module proves normalization and positive mass for the zero and unit steps.

`Exotic/ERL/Exploration/DyadicLadder.agda` gives a finite ladder law with common denominator 32: stay has numerator 16 and each of the sixteen signed power-of-two outcomes has numerator 1. The module proves normalization and the positive ±1 support witnesses. Because ±1 is present, the usual additive generator obstruction is removed at the support level; full-state reachability still needs the actual transition theorem.

These laws are useful exactly because they are theorem-friendly probability interfaces. They should be compared with `D_tri` and lazy-unit laws by explicit finite criteria rather than assumed superior.

### Automated theorem discovery

The discovery loop is:

`method metadata -> concrete proof-harness generation -> agda --safe -> theorem acceptance`

Implemented in `.ci/discovery/ExplorationTheoremGenerator.hs`, with output written to `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda` and executed by `.github/workflows/agda.yml`.

A method is marked proven only when its concrete proof harness passes `agda --safe`. Haskell never upgrades a conjecture into a theorem.

## Strongest endogenous theorem class

Among the three methods, Noisy Nets has the strongest overall theorem-class frontier for the complete composition, while MR15 has the strongest dedicated outer-exploration graph theorem frontier.

Noisy Nets is broader because its theorem surface can simultaneously range over finite Int8 noise algebra, GateNN identities, exact coupled-state transition relations, self-loop construction, learner-state reachability, full learner+EA reachability, exact VJP/CHAD equalities, the representation path containing signReLU8, softsign8, GateNN, and projection, and the final full-state period theorem.

MR15 is the stronger pure exploration mathematics target because its repaired form naturally exposes finite mutation support, the `gcd(256,S)=1` generator theorem, positive-mass zero-step self-loop, iid finite noise-tape factorization, exact weighted expectations, population reachability, deterministic selection compatibility, and full-coupled lift conditions.

OpenES is a narrower functional ablation surface. Lazy Walk and Dyadic Ladder are now explicit probability-law surfaces that can be promoted into graph kernels once their concrete transition relations are attached.

This is a theorem-surface breadth ranking only. It does not assert empirical superiority.

## Current method status

MR15: the repaired independent-tick kernel passes `agda --safe`, but the current proof is still an abstraction over the production population mutation/selection semantics.

OpenES: the finite shell passes `agda --safe`, but its current kernel remains an abstraction until the exact production transition is connected.

Noisy Nets: it belongs inside the coupled learner. `NoisyNetCoupled.agda` defines finite gate state, noisy `w3`, the exact diagonal identity, and coupled irreducibility/self-loop proofs for the explicit fresh-target kernel.

## Finite graph theorem class

For a transition relation `_—→_`:

`Irreducible = ∀ s t → Reach _—→_ s t`.

`SelfLoop = ∀ s → s —→ s`.

The reusable sufficient period-1 package is `Irreducible × SelfLoop -> PeriodOne`.

This is deliberately a full-state statement. Exploration-only reachability never substitutes for learner+EA reachability.

## Mutation theorem class

For an additive coordinate over `Z_256`, the generator target is `gcd(256,S) = 1` for the effective positive-probability increment support `S`.

A one-step self-loop requires effective support containing `0` with positive mass.

The previous same-noise exponent repetition is not theorem-friendly globally because exponent scaling can reduce the effective support and destroy communication classes. The preferred construction is an explicit finite fresh-noise tape or an equivalent one-shot per-coordinate mutation.

## Distribution theorem class

`D_tri` remains the canonical design choice:

`D_tri(k) = (16 - |k|) / 256`, `k ∈ {-15,…,15}`.

Its useful exact facts are finite dyadic normalization, symmetry, zero center mean, positive mass at zero, Int8-range support, and exact second moment `85/2`.

Do not promote the design claim that `D_tri` is universally statistically best. The strongest algebraic comparison schema remains criterion-conditioned:

`Best(Φ,D*) = ∀ D ∈ Admissible → Φ(D*) >= Φ(D)`.

Entropy, second moment, expected displacement, finite-horizon coverage, estimator noise, and full-coupled task utility are separate criteria.

## CHAD and activation composition

CHAD does not by itself prove every property of every finite exploration kernel. CHAD proves the correctness of a differential/VJP interface for a defined computation; normalization, support, irreducibility, communication classes, and period are separate finite-state theorems.

The repository now has an exact `CHADOperator` composition theorem in `Exotic/efficient_chad/Int8.agda`. That theorem is sufficient to compose future concrete finite operators in the order:

`signReLU8 -> softsign8 -> GateNN -> Pi`.

A concrete signReLU8 or softsign8 VJP theorem still requires the corresponding in-tree operator definition. A Möbius theorem is similarly an additional algebraic theorem; the generic CHAD composition law does not invent it.

## External Efficient-CHAD boundary

The workflow audits Tom Smeding's upstream source in a clean `.ci/external/efficient-chad-agda` checkout and probes its existing `chad-cost.agda` under the installed Agda 2.8.0 toolchain. No new package or project-local Agda library is added by this audit. The upstream file itself imports its own checked-in dependencies, which remain outside the repository theorem authority.

## Gating-layer counterfactual

`GatingLayerCounterfactual.agda` proves two distinct facts. Gate reachability lifts through an explicit full-state lift. Conversely, if every step preserves a non-gating learner coordinate and that coordinate has two distinct values, the full product relation cannot be irreducible. Therefore exploration need not be restricted to the gate representation layer; doing so is insufficient for whole-state communication unless the remaining factors are already singleton or otherwise connected by the same transition.

## Recent 3D reasoning relevance

Recent 3D work surfaced by SciSpace includes CoRe3D, GaussExplorer, MILO/implicit spatial world modeling, 3DSPMR, and Map2Thought. Their useful architectural ideas are discrete spatial abstraction, relative geometric transformations, persistent spatial memory, and explicit compositional reasoning. None of those external papers becomes an Agda theorem merely by being recent, and SciSpace does not establish that their authorship was generated by ChatGPT, Gemini, or Claude.

## Full coupling

The whole composition remains:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

The GateNN diagonal identity is separate from the softsign theorem.

Noisy Nets must be represented inside the coupled learner state when proving whole-system reachability. The target theorem is `∀ s t → CoupledReach s t` for the actual full learner+EA transition, followed by the actual full-state self-loop theorem. Exploration irreducibility alone is insufficient.

## IID and expectation in `--safe`

Finite iid and exact expectation are constructible from finite support, exact dyadic masses, finite products, and finite weighted sums. The missing proof is implementation-specific factorization: the actual transition must consume fresh noise coordinates/ticks as claimed.

## Fitness theorem

The modified finite VEB-RL-style `-TD` fitness remains an exact finite statistic: histogram masses are exact dyadic integers; normalization is exact; ordinal/rank ordering is exact; and full sorting is retained whenever rank consistency is part of the theorem.

## Replication order

1. Keep pure DMCP modules deleted.
2. Enforce the permanent finite/dyadic theorem-scope exclusions.
3. Keep Lazy Walk and Dyadic Ladder as exact finite probability ablations.
4. Put the repaired independent-tick MR15 definition in-tree.
5. Prove MR15 generator support, self-loop, and full finite reachability for the actual transition.
6. Prove the corresponding OpenES theorems for its actual transition.
7. Keep Noisy Nets inside the full coupled learner state and prove its actual coupled reachability obligations.
8. Run the automated theorem generator and require concrete proof terms plus `agda --safe` before marking a method proven.
9. Prove full learner+EA irreducibility.
10. Apply the actual full-state self-loop theorem for period 1.
11. Extend CHAD through the entire representation path.
12. Compare exploration distributions only under explicit exact finite criteria.
