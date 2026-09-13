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

### Automated theorem discovery

The discovery loop is:

`method metadata -> concrete proof-symbol test -> agda --safe -> theorem-status report`

Implemented in `.ci/discovery/ExplorationTheoremGenerator.hs`, with output written to `Exotic/ERL/Exploration/Generated/ExplorationCandidates.agda` and executed by `.github/workflows/agda.yml`.

A method is marked `Proven` only when concrete proof terms are present and its Agda file passes `agda --safe`. `MissingProof` means the theorem target has not been closed. `AgdaFailure` means the claimed proof surface does not typecheck safely. Haskell never upgrades a conjecture into a theorem.

The generator is extensible by theorem-family metadata. It can enumerate support conditions, self-loop conditions, finite-tape factorization, coupled reachability, exact expectations, rank identities, VJP identities, and ablation combinations. Its output is always ordinary Agda source subject to the same `--safe` gate.

## Strongest endogenous theorem class

Among the three methods, Noisy Nets has the strongest overall theorem-class frontier for the complete composition, while MR15 has the strongest dedicated outer-exploration graph theorem frontier.

Noisy Nets is broader because its theorem surface can simultaneously range over:

- finite Int8 noise algebra;
- GateNN parameter/noise identities;
- exact coupled-state transition relations;
- self-loop construction;
- learner-state reachability;
- full learner+EA reachability;
- exact VJP/CHAD equalities;
- the representation path containing signReLU8, softsign8, GateNN, and projection;
- the final full-state period-1 theorem.

That breadth makes Noisy Nets the strongest candidate for the endogenous theorem class that crosses subsystem boundaries and reaches the whole finite composition.

MR15 is the stronger pure exploration mathematics target because its repaired form naturally exposes:

- finite mutation support;
- the `gcd(256,S)=1` generator theorem;
- positive-mass zero-step self-loop;
- iid finite noise-tape factorization;
- exact weighted expectations;
- population reachability;
- deterministic selection compatibility;
- full-coupled lift conditions.

OpenES is the narrowest current frontier. Its finite ask/tell shell can support exact mutation, antithetic, involution, and reachability theorems, but its present source is much smaller and currently lacks a global irreducibility proof.

Therefore the theorem-first ranking is:

`Noisy Nets` — broadest whole-composition endogenous theorem class.

`MR15` — strongest specialized exploration-kernel theorem class.

`OpenES` — narrower functional exploration theorem class.

This is a theorem-breadth ranking, not a claim of empirical performance.

## Current method status

MR15: the existing negative reachability theorem must not be confused with the repaired independent-tick definition. The repository still needs the actual repaired transition plus concrete generator, self-loop, and global reachability proofs.

OpenES: the current finite shell does not contain an irreducibility proof. Its definitions remain useful as an ablation surface, but global reachability must be proved for the exact transition relation.

Noisy Nets: it belongs inside the coupled learner. `NoisyNetCoupled.agda` defines finite gate state, noisy `w3`, the exact diagonal identity, and explicit theorem types for coupled irreducibility and self-loop. Those properties remain obligations until concrete proof terms pass `agda --safe`.

## Finite graph theorem class

For a transition relation `_—→_`:

`Irreducible = ∀ s t → Reach s t`.

`SelfLoop = ∀ s → s —→ s`.

The reusable sufficient period-1 package is:

`Irreducible × SelfLoop -> PeriodOne`.

This is deliberately a full-state statement. Exploration-only reachability never substitutes for learner+EA reachability.

## Mutation theorem class

For an additive coordinate over `Z_256`, the generator target is:

`gcd(256,S) = 1`

for the effective positive-probability increment support `S`.

A one-step self-loop requires effective support containing `0` with positive mass.

The previous same-noise exponent repetition is not theorem-friendly globally because exponent scaling can reduce the effective support and destroy communication classes. The preferred construction is an explicit finite fresh-noise tape or an equivalent one-shot per-coordinate mutation.

## Distribution theorem class

`D_tri` remains the canonical design choice:

`D_tri(k) = (16 - |k|) / 256`, `k ∈ {-15,…,15}`.

Its useful exact facts are finite dyadic normalization, symmetry, zero center mean, positive mass at zero, Int8-range support, and exact second moment `85/2`.

Do not promote the design claim that `D_tri` is universally statistically best. The strongest algebraic comparison schema remains criterion-conditioned:

`Best(Φ,D*) = ∀ D ∈ Admissible → Φ(D*) >= Φ(D)`.

Entropy, second moment, expected displacement, finite-horizon coverage, estimator noise, and full-coupled task utility are separate criteria.

The canonical choice is therefore theorem-driven, not a universal max-entropy rule.

## Ablation classes

Triangular `D_tri`: broad symmetric dyadic support with positive zero mass.

Flat dyadic: useful entropy ablation; no universal task-superiority consequence follows from flatter mass.

Center-heavy: can remain graph-theoretically eligible while having much smaller exploration scale.

Lazy unit: `{-1,0,+1}` is a simple irreducibility+aperiodicity target under independent additive sampling.

Rademacher: `{-1,+1}` has generator support but no lazy self-loop, so the basic walk is periodic.

Even-step laws: self-loop can exist, but gcd generation fails on `Z_256`.

Noisy Nets: parameter noise belongs inside the coupled learner theorem rather than being treated as an unrelated outer distribution. The finite noise law may be `D_tri`, but coupled reachability must still be established from the complete transition.

## Full coupling

The whole composition remains:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

The GateNN diagonal identity is separate from the softsign theorem.

Noisy Nets must be represented inside the coupled learner state when proving whole-system reachability. The target theorem is:

`∀ s t → CoupledReach s t`

for the actual full learner+EA transition, followed by the actual full-state self-loop theorem. Exploration irreducibility alone is insufficient.

## IID and expectation in `--safe`

Finite iid and exact expectation are constructible from finite support, exact dyadic masses, finite products, and finite weighted sums. The missing proof is implementation-specific factorization: the actual transition must consume fresh noise coordinates/ticks as claimed.

No general measure-theory layer is logically needed merely for these finite statements.

## Fitness theorem

The modified finite VEB-RL-style `-TD` fitness remains an exact finite statistic:

- histogram masses are exact dyadic integers;
- normalization is exact;
- ordinal/rank ordering is exact;
- full sorting is retained whenever rank consistency is part of the theorem;
- comparison cost remains `O(N log N)` unless a tighter exact finite count is formally established.

Approximate quantile structures are not silently substituted.

## Forward CHAD status

The intended path is:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

Exact CHAD for the finite GateNN/projection node is not equivalent to an end-to-end theorem. The full chain still requires VJP rules and a chain-rule proof through every upstream primitive.

Iterative CHAD is useful for generating differential/VJP candidates, but Agda remains the final acceptance oracle.

## Toolchain boundary

The current workflow installs Agda and GHC and runs the Haskell oracle directly with `runghc`. Cabal is a build driver, not a logical proof dependency. Agda2HS does not turn Cabal into a mathematical requirement.

Nix or Guix is an environment-reproducibility choice, not a proof authority. Exact inputs and Agda/stdlib versions must be pinned.

## Replication order

1. Keep pure DMCP modules deleted.
2. Enforce the permanent CI theorem-scope exclusions.
3. Put the repaired independent-tick MR15 definition in-tree.
4. Prove MR15 generator support, self-loop, and full finite reachability.
5. Prove the corresponding OpenES theorems for its actual transition.
6. Keep Noisy Nets inside the full coupled learner state and prove its actual coupled reachability obligations.
7. Run the automated theorem generator and require concrete proof terms plus `agda --safe` before marking a method proven.
8. Prove full learner+EA irreducibility.
9. Apply the actual full-state self-loop theorem for period 1.
10. Extend CHAD through the entire representation path.
11. Compare distributions only under explicit exact finite criteria.
