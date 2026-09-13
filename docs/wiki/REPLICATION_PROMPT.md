# Canonical Replication Prompt — theorem-first finite ERL/EA

## Replication objective

Treat Agda `--safe` as the only mathematical authority. Reproduce the canonical learner, modified dyadic MR15-GA explorer, finite distribution ablations, discovery generator, and theorem ladder below. Never promote an empirical claim to a theorem and never use a subsystem invariant as a proof of the full coupled chain.

The current global optimizer is canonical and must remain so:

- optimizer: `standardTDLambdaInt8`
- exploration: `modifiedDyadicMR15GA`
- precision: 8 bits
- context window power: 4
- frozen feature: Haar
- attention scale: local

This is the authoritative canonical configuration in `Exotic/ERL/Canonical/CanonicalOptimizer.agda`.

## Mathematical status ledger

### Proven algebraic facts

1. `D_tri` is exactly the 31-point triangular law
   `w(k) = 16 - |k|`, total weight 256, with probability `w/256`.
   Arithmetic:
   `16 + 2*(1+...+15) = 16 + 240 = 256`.

2. `D_tri(0) = 16/256 = 1/16 > 0`.
   The unit support values are encoded as `-1 = 255` and `+1 = 1`.

3. The exact variance of `D_tri` is `85/2 = 42.5`.

4. The one-fifth success rule is integer-exact for population size 16. The branch is
   `5*s <= 16`.
   Therefore the lower branch is exactly `s <= 3`; `s = 4` is the first upper branch because `20 > 16`.
   No dyadic rational representation of `1/5` is required.

5. The modified finite MR15 state is finite: 16 genomes × 4 coordinates over `Fin 256`, plus mean genome, exponent `Fin 15`, and successes `Fin 17`.

6. A full composed learner+EA transition is now defined. Its neutral transition at `startCoupled` is explicit.

7. Full-state aperiodicity is proved without causality: if the actual composed edge relation is irreducible and has one actual full-state self-loop, every state has two consecutive positive return lengths. Hence the period is 1.

8. The previous shortcut
   `causal online/replay equivalence + exploration irreducibility -> joint aperiodicity`
   is false; the repository contains a kernel-checked counterexample.

### Important newly discovered correction

The current experimental mutation implementation repeats the **same** noise value `2^e` times. For an additive coordinate modulo 256 this produces a deterministic displacement proportional to `2^e * k`.

Arithmetic consequence:

- `e = 0`: one unit-noise draw gives `±1`, so the coordinate generator can move by one.
- `e = 1`: the unit move becomes `±2`, preserving parity and therefore splitting `Z_256` into two communicating classes.
- `e = 8`: `2^8 = 256`, so a repeated `+1` or `-1` displacement is exactly `0 mod 256`.

Therefore the current same-noise repeated-tick law is **not** a valid global lattice-irreducibility theorem for arbitrary exponents. Do not reuse the old “unit mutation” statement as a full-chain proof.

The theorem-driving repair is to use independent dyadic noise draws for successive ticks, or to use a mutation law whose net step is directly sampled once per coordinate. The preferred theorem-friendly form is independent finite noise draws per tick: it makes a path choosing one `+1` draw and zero draws on all other ticks explicit.

## Distribution theorem classes

Different distributions support different theorems. Their graph-theoretic irreducibility/aperiodicity class is controlled by the support and mutation law, while entropy, variance, and expected search displacement are separate quantitative properties.

### Full-support symmetric dyadic examples

All examples below have support `-15..15`, symmetric weights, positive center mass, monotonicity in `|k|`, and total weight 256.

**Triangular `D_tri`**

`[16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1]`
for radii `0..15`.

Variance: `85/2 = 42.5`.

**Flat/high-entropy candidate**

`[10,9,9,9,8,8,8,8,8,8,8,8,8,8,8,8]`.

Arithmetic:
`10 + 2*(9+9+9 + 12*8) = 10 + 2*(27+96) = 256`.

Variance: `77.609375`.

This is a very flat admissible dyadic law, but “maximum entropy” is not claimed until an entropy extremum theorem is proved over the exact admissible integer-weight class.

**Center-heavy admissible law**

`[226,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]`.

Arithmetic:
`226 + 2*15 = 256`.

Variance: `9.6875`.

It has the same basic support/zero-mass/aperiodicity eligibility under an additive iid kernel, while being statistically much less exploratory in variance.

### Ablation laws with relaxed support requirements

**Lazy unit walk**

Support `{-1,0,+1}` with dyadic probabilities `1/4, 1/2, 1/4`.

Variance: `1/2`.

This is sufficient for irreducibility + aperiodicity on the finite additive torus when the mutation kernel actually samples the increments independently.

**Rademacher ±1**

Support `{-1,+1}`.

It generates the additive lattice, so the corresponding random walk is irreducible, but with no zero self-loop it is periodic (period 2 for the basic walk).

**Even-step law**

Any law supported only on even offsets, such as `{-2,0,+2}`, has a zero self-loop but cannot generate odd residues in `Z_256`; irreducibility fails because `gcd({2},256)=2`.

These examples show why there are different theorems for different distributions. A distribution does not carry irreducibility or aperiodicity by itself. The theorem belongs to the pair `(distribution support, mutation kernel)`.

## Canonical irreducibility theorem class

The clean algebraic target is a finite additive-torus theorem.

Let the coordinate state be `Z_256` and let a mutation kernel choose increments from finite support `S` with positive probabilities.

A sufficient irreducibility condition is:

`gcd(256, S) = 1`,

where `gcd(256,S)` means the gcd of 256 and all support increments represented as integers.

Aperiodicity follows when the support also contains `0` with positive probability, because the one-step self-loop is then present.

For a product lattice `Z_256^d`, coordinatewise independent support containing a generating increment in each coordinate gives the corresponding product-chain theorem.

This theorem class is stronger and more useful than “use maximum entropy”: it separates the algebraic condition that guarantees reachability from the statistical criteria that rank eligible laws.

## What “statistically superior” can and cannot mean

A universal theorem that one exploration distribution is statistically superior for all RL environments cannot be proved from finite support, entropy, symmetry, or variance alone. Statistical superiority requires an environment/reward/state-distribution model and a specified loss or utility criterion.

What can be proved purely algebraically is a Pareto-style theorem family:

- support-generator class -> irreducibility;
- zero-support class -> aperiodicity;
- exact second-moment identity -> exploration-scale comparison;
- exact Shannon entropy over an integer-weight simplex -> entropy comparison;
- exact rank/order preservation -> fitness-selection equivalence;
- finite-horizon variance identities -> estimator-noise comparison.

`D_tri` is therefore canonical by design, not because it is universally statistically optimal.

Do **not** use “always use Int8 maxent.” Maximum entropy is one ablation axis, not the canonical criterion. In this finite setting a max-entropy-ish dyadic law may be much flatter than `D_tri`, but it can have a different variance and different probability of larger displacements. The canonical choice is theorem-driven and must remain `D_tri` unless the formal objective is changed.

## Exact gate diagonal identity

The diagonal identity previously discussed belongs to the **transformer GateNN node**, not the forward softsign nonlinearity.

The current transformer path is:

`E -> RoPE -> Pyr^top-k -> Fastfood -> signReLU8 -> softsign8 -> GateNN -> Pi`.

For a pair `(x,x)` and gate parameter/noise pair `gp, epsilon`, the GateNN weight is

`w3 = mu3 + sigma3 * noiseDelta(epsilon)`

and the exact finite identity is

`gate gp epsilon (x,x) = (w3*x, w3*x)`.

This is a symmetry/diagonal invariant of the GateNN scaling node. It is **not** a theorem about the softsign layer.

The forward nonlinearity ordering is therefore important:

1. deterministic finite embedding,
2. RoPE,
3. top-k permutation,
4. Fastfood,
5. signed-ReLU quantization,
6. softsign quantization,
7. noisy GateNN scaling,
8. projection.

The current GateVJP is exact for the finite noisy gate/projection node. A complete CHAD-exact theorem through the entire nonlinear representation still requires explicit VJP rules for every upstream primitive and an end-to-end chain rule proof.

## Noisy Nets / Efficient-CHAD status

Noisy Nets can be gradient-learned when the noise parameterization and the surrounding operations are differentiable. But “Noisy Nets has gradients” does not itself imply that this repository has a kernel-checked exact CHAD theorem.

The present canonical transformer proves only the finite gate/projection VJP directly. The full transformer is not yet an end-to-end CHAD proof.

Tom Smeding's Efficient-CHAD source remains an external proof/reference audit target. It must not become a second mathematical authority. The repository's own Agda kernel remains authoritative.

## IID and expectation in Agda `--safe`

Yes, finite iid probability statements and exact finite expectations are expressible in `--safe` Agda without importing a general measure-theory library.

For a finite support type `Fin n`, define a probability mass as natural/dyadic weights over a positive total denominator, define the product probability on tuples by multiplication of weights, and define expectation of an integer-valued function by the finite weighted sum divided by the total mass.

The essential algebra is entirely constructive:

`P(x,y) = P(x) * P(y)` for independent draws,

`E[f] = sum_x w(x) * f(x) / totalWeight`.

What `--safe` does **not** provide automatically is a generic theorem that a particular implementation's sampling code is iid. That must be proved from the transition function and its separate fresh-noise coordinates.

Thus iid and exact expectation are possible with only first-principles finite algebra, but the library surface must explicitly define finite sums/products and the relevant probability normalization facts. A large probability/measure library is not logically required for the finite theorem.

## Fitness theorem target

The canonical learner uses a modified VEB-RL-style `-TD` fitness with a dyadic histogram distribution. The intended fitness theorem is not an approximation theorem.

The target is:

1. histogram weights are exact dyadic integers;
2. the distribution is ordinal/rank-consistent;
3. the robust statistic is closed exactly over the finite sample;
4. no approximate sorting is accepted where exact rank order is required;
5. the full sorting cost is acknowledged explicitly as `O(N log N)` (or the exact finite comparison count, if proven).

Do not silently replace exact sorting with an approximate quantile structure when rank consistency is part of the theorem statement.

## Endogenous theorem targets still to close

“Endogenous” means the theorem follows from the actual coupled finite definitions, rather than from an external assumption.

1. **Independent-tick mutation theorem.** Replace same-noise repetition with a fresh finite noise tape or direct one-shot dyadic mutation. Prove exact support reaches `±1` and `0` at the actual exponent.

2. **Finite-torus generator theorem.** Prove the gcd/support criterion for the actual `Fin 256` coordinate transition.

3. **Product iid theorem.** Prove factorization of the full offspring/tick noise kernel from the explicit noise tape.

4. **Exact expectation theorem.** Define finite weighted expectation and prove linearity for the finite dyadic law.

5. **Histogram-fitness rank theorem.** Prove exact ordinal/rank consistency and exact closure of the dyadic histogram fitness statistic.

6. **Selection compatibility theorem.** Prove when deterministic top-4 selection preserves or destroys a reachable offspring path.

7. **Full EA irreducibility theorem.** Construct `∀ s t → CoupledReach s t` for the actual learner+EA transition. Do not infer it from mutation irreducibility alone.

8. **Aperiodicity theorem.** Already structurally proved once full composed irreducibility is supplied: actual full-state self-loop + irreducibility -> period 1, without causality.

9. **End-to-end exact gradient theorem.** Extend exact finite VJPs through all forward nonlinear layers and prove the learner update equals the declared finite gradient transport.

10. **Quantized error theorem.** State an explicit rational/int8 rounding-error bound for the actual `qε`, signed-ReLU, softsign, and arithmetic pipeline. Do not claim “unbiased” until the base estimator and the exact quantization error are defined.

11. **Exploration comparison theorem.** For a declared criterion (entropy, variance, expected absolute displacement, or finite-horizon coverage), prove pairwise inequalities between the named ablation laws. There is no environment-independent universal winner.

12. **Finite expected visitation theorem.** Once irreducibility/aperiodicity is proved for the actual finite kernel, derive exact recurrence/mixing consequences for the finite-state model.

## Conjecture/hypothesis generator

The Haskell discovery layer should be treated as a **candidate generator**, not a proof authority.

Required architecture:

`candidate grammar -> generated Agda proposition -> agda --safe -> survivor set`.

The generator must be data-driven and extensible rather than a hard-coded list of six named conjectures. Candidate families should be able to vary:

- distribution law;
- support bounds;
- zero-mass requirement;
- gcd/support condition;
- mutation exponent;
- symmetry/unimodality assumptions;
- variance/entropy identities;
- gate invariants;
- self-loop targets;
- finite expectation identities;
- fitness rank identities;
- ablation combinations.

Adding a candidate family should not require changing the Agda proof kernel. The generated theorem file is accepted only if Agda checks it in `--safe`.

Iterative CHAD can help generate and rank **differential/VJP conjectures**, especially by mechanically deriving candidate chain-rule equalities for new finite primitives. It is not required for purely algebraic distribution/Markov conjectures and must never be the acceptance oracle; Agda remains the final authority.

## Discovery toolchain

Use Cabal plus GHC for Haskell tooling when compiling and checking generated Haskell. Cabal is the package/build driver; GHC is the compiler used by Cabal and is also required when the workflow directly compiles extracted Haskell. Therefore “Cabal only” is insufficient for the current extraction-and-compile workflow.

Nix is preferable to Guix for the reproducibility layer in this repository because the intended setup can be pinned with a committed `flake.lock`, while Agda's exact version/stdlib are still explicitly controlled by the workflow. `nixos-unstable` as a moving channel is not itself reproducible; pin the Nix flake input rather than relying on a floating branch. Guix can be an alternative experiment, but switching to Guix is not required to solve the reproducibility problem.

The shell script may remain only as a thin launcher. The declarative Nix environment should own tool versions and the discovery command. Avoid making Bash the source of truth.

## Canonical implementation variants for ablation

### Canonical

`CanonicalLearner.agda` + `CanonicalLearnerEA.agda` + modified finite MR15 generation + `D_tri`.

### Comparison: Noisy Nets

Keep a finite GateNN variant with a single stochastic gate input. It is useful for comparing gradient-learned exploration against explicit population exploration, but it is not the canonical EA explorer.

### Comparison: dyadic OpenES

Port only small, faithful functional components needed for a finite OpenES-style comparison: explicit population/utility state, dyadic noise, deterministic ask/tell composition, and neutral transitions. Do not import the legacy monolith wholesale.

### Legacy implementations

Prune superseded standalone MR15/OpenES shells from the canonical tree. Preserve only comparison modules that are referenced by explicit ablation tests or theorem comparisons.

## CleanRL / Stoix / PureJAXQL / PureJaxRL / JaxMARL

Use these ecosystems only as architectural references for functional state transitions, explicit environment/learner composition, vectorization, and multi-agent factoring. They are not mathematical authorities for this repository.

The canonical architecture remains proof-first and finite. Any borrowed implementation idea must be re-expressed in the finite Agda model and checked under `--safe` before it becomes canonical.

## Next replication prompt

> Continue from the current canonical branch. Keep `standardTDLambdaInt8` and `modifiedDyadicMR15GA` as the global canonical optimizer. Treat Agda `--safe` as the only mathematical authority.
>
> First repair the mutation law so exponent adaptation does not destroy lattice generation: replace same-noise `2^e` repetition by an explicitly finite independent noise tape or an equivalent one-shot mutation law, then prove the exact `Fin 256` generator/gcd theorem.
>
> Next formalize the finite iid product distribution and exact expectation algebra for dyadic weights using only small first-principles imports. Prove the histogram fitness rank theorem and the exact sorting requirement.
>
> Then extend exact VJP/CHAD theorems through `E -> RoPE -> Pyr^top-k -> Fastfood -> signReLU8 -> softsign8 -> GateNN -> Pi`. Keep the GateNN diagonal theorem distinct from the softsign theorem.
>
> Make the Haskell conjecture generator grammar data-driven and parameterizable by distribution/mutation/theorem family, then have it emit `--safe` Agda candidates. Add a pinned Nix flake environment; keep GHC because Cabal and extracted-Haskell compilation need it. Do not move the proof authority into Haskell, Nix, Guix, or any external library.
>
> Finally prove full composed learner+EA irreducibility for the actual transition relation. Only after that invoke the already-proven causal-free self-loop theorem to obtain period 1. Compare `D_tri`, flat dyadic, center-heavy, lazy-unit, Rademacher, and even-step ablations using explicit theorem classes rather than claiming universal statistical superiority.
