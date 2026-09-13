# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

Repository CI authority: `.github/workflows/agda.yml`, which reads `.ci/canonical-module.txt` and checks both listed files with `agda --safe`.

Current manifest:

- `Exotic/ERL/FullCoupled/AllSafeCombined.agda`
- `Exotic/ERL/FullCoupled/AllSafeCombined_test.agda`

`AllSafeCombined.agda` is currently a small safe regression bundle. `Agda/README.md` separately describes `Exotic/ERL/FullCoupled/CompleteSafe_v147.agda` as the intended v147 source and lists the audited v147 theorem surface. Treat that v147 path as a closure target until the exact file exists in-tree and is wired into the canonical manifest.

## Live Agda proof surface

Current exploration modules include:

- `Exotic/ERL/Exploration/DMCPDistribution.agda`
- `Exotic/ERL/Exploration/MR15Reachability.agda`
- `Exotic/ERL/Exploration/OpenESDyadic.agda`

Current stage modules include `Stage01_FiniteAlgebra.agda`, `Stage02_CHAD.agda`, `Stage03_LinearLearner.agda`, `Stage04_QProjection.agda`, `Stage05_Representation.agda`, `Stage06_CoupledLearner.agda`, and `Stage09_FiniteLocalConvergence.agda`.

The current `MR15Reachability.agda` is especially important: it proves that the present `mr15Step` relation preserves a uniform-population invariant, derives a concrete unreachable spike population, and therefore proves the current relation is not globally irreducible. Its declared aperiodicity obligation is impossible for that current relation. This is a repository theorem about the present transition, not a defect to paper over.

## Canonical architecture ledger

Intended canonical configuration:

- optimizer: `standardTDLambdaInt8`
- explorer: `modifiedDyadicMR15GA`
- precision: 8 bits
- context window power: 4
- frozen Haar feature
- local attention scale
- mutation target: independent finite draws per tick
- exact dyadic histogram fitness with exact sorting and rank consistency

The named optimizer/explorer above are architectural targets; the live repository should not be described as implementing them until exact Agda modules and CI paths exist.

## Theorem ladder

Already repository-checked:

1. finite Int8 identity and roundtrip identities in `AllSafeCombined.agda`;
2. exact dyadic normalization for the checked DMCP distribution;
3. the current MR15 negative reachability theorem described above;
4. staged finite algebra and CHAD modules exist as explicit Agda source files.

Next endogenous theorem targets:

1. independent-tick mutation theorem from an explicit finite noise tape;
2. exact `Fin 256` additive-torus generator theorem using `gcd(256,S)=1` for the effective support;
3. positive self-loop theorem from effective support containing `0`;
4. product iid factorization for fresh noise coordinates/ticks;
5. exact finite expectation and linearity for dyadic weighted sums;
6. exact dyadic histogram fitness closure and ordinal/rank consistency;
7. exact selection-compatibility theorem for population transitions;
8. full learner+EA irreducibility for the actual composed transition relation;
9. full-state period-1 from full-state irreducibility plus an actual full-state self-loop;
10. end-to-end finite VJP/CHAD through every actual forward primitive;
11. explicit int8 quantization error theorem before any unbiasedness claim;
12. criterion-parameterized exploration extremum/comparison theorems.

Do not derive whole-chain theorems from subsystem invariants. In particular, exploration irreducibility alone does not imply learner+EA irreducibility.

## Distribution theorem separation

Graph-theoretic properties belong to `(support, mutation kernel)`.

For an additive coordinate over `Z_256`, the reachability target is:

`gcd(256,S) = 1`.

For one-step aperiodicity, the effective increment support must contain `0` with positive probability, giving an actual self-loop. Product chains require the actual product kernel to be checked.

Statistical quantities are separate: entropy, second moment, expected absolute displacement, finite-horizon coverage, selection noise, and task utility. None of these implies a universal environment-independent winner.

### Criterion-conditioned superiority theorem class

The strongest useful algebraic theorem schema is parameterized:

`Best(Φ,D*) = ∀ D ∈ Admissible → Φ(D*) >= Φ(D)`.

Here `Admissible` and `Φ` are explicit finite definitions. This permits exact pairwise or extremal theorems for entropy, variance/second moment, expected displacement, or finite-horizon criteria. It does not produce a universal winner across all criteria and environments.

Therefore: do not always use int8 maximum entropy. Maximum entropy is an ablation criterion, not the canonical objective. `D_tri` remains canonical by design unless the formal criterion is changed.

## Distribution ablation classes

`D_tri`: support `[-15..15]`, symmetric, positive center mass, exact dyadic normalization. Canonical balanced choice, not a universal optimum.

Flat dyadic: flatter weights can improve entropy relative to center-heavy choices, but entropy does not imply greater task utility or reachability speed.

Center-heavy: can still satisfy irreducibility/aperiodicity when its support includes a generator and zero, while having much smaller second moment.

Lazy unit: `{-1,0,+1}` is theorem-friendly for irreducibility plus aperiodicity under independent additive sampling, with low exploration scale.

Rademacher unit: `{-1,+1}` generates the additive group but lacks a self-loop, so the basic walk is periodic.

Even-step law: supports such as `{-2,0,+2}` have a self-loop but fail the generator criterion because the support gcd with 256 is greater than 1.

Mutation semantics are a distinct ablation axis. Repeating one sampled value `2^e` times changes the effective support to scaled steps and can destroy lattice generation. Fresh independent draws per tick make the noise tape itself the constructive path object.

## Forward path and nonlinearity placement

Intended representation path:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

The GateNN diagonal identity is a property of the GateNN scaling node, not the softsign nonlinearity. A complete CHAD theorem must therefore include the upstream nonlinear path rather than treating the gate theorem as an end-to-end result.

Frozen Haar/Fastfood is canonical. A learned diagonal on top of a frozen mixer is a valid ablation. Learning the mixer itself changes the mathematical object into a generic learnable linear map and loses the frozen Walsh/Rademacher structure.

A learned int8 softsign layer is a valid ablation, but it adds learned state and exact VJP obligations and is not canonical unless promoted by formal definition and proof.

## IID and expectation in `--safe`

Finite iid distributions and exact expectations can be built constructively without a general measure-theory framework: finite support, natural/dyadic masses, exact normalization, finite products, and finite weighted sums suffice.

The nontrivial theorem is that the implementation actually realizes iid sampling. That must be proved from explicit fresh-noise coordinates/ticks. `--safe` does not supply that theorem automatically.

## Fitness theorem

The modified VEB-RL-style `-TD` fitness is treated as an exact finite statistic. When rank consistency is part of the contract:

- histogram weights remain exact dyadic integers;
- the statistic is closed exactly over the finite sample;
- ordinal ordering is preserved exactly;
- exact full sorting is retained, with `O(N log N)` comparison cost as the algorithmic contract unless a tighter finite count is formally derived.

Approximate quantiles do not silently replace exact rank computation.

## Conjecture / hypothesis generator

Use:

`candidate grammar -> generated Agda proposition -> agda --safe -> survivor set`.

Parameters should cover distribution family, support bounds, zero mass, gcd conditions, mutation exponent/tick semantics, symmetry, unimodality, entropy, moments, GateNN invariants, self-loops, expectation identities, fitness rank identities, and ablation combinations.

The generator remains data-driven and extensible. Adding a theorem family should not require changing the Agda acceptance kernel. Haskell is a candidate generator, never the proof authority.

Iterative CHAD is helpful for differential/VJP hypothesis generation and ranking when finite primitives change. It is not necessary for the algebraic distribution layer and cannot replace `agda --safe`.

## Noisy Nets / Efficient-CHAD

Noisy Nets can be gradient-learned under a differentiable parameterization, but that fact alone does not give an end-to-end repository theorem.

The current GitHub Actions workflow audits Tom Smeding's external `efficient-chad-agda` source and probes it under the current Agda toolchain. That source is an audit/reference target, not a second mathematical authority.

No dedicated Noisy-Nets Agda module is present in the current repository tree inspected here. Treat it as a new explicit ablation until formalized.

## Cabal, GHC, Agda2HS, Nix, Guix

The live `.github/workflows/agda.yml` does not build the Haskell oracle with Cabal. It installs Agda, installs GHC 9.6, and runs the oracle with `runghc`.

Thus GHC is the strict dependency for the current direct-execution oracle. Cabal becomes necessary only when the Haskell side is packaged as a Cabal project/build. Agda2HS likewise does not make Cabal logically necessary; extracted Haskell that is compiled or executed still needs a Haskell compiler/runtime.

The current repository root does not expose a committed Nix flake in the tree inspected here. `nixos-unstable` is therefore not a current proof dependency. A moving `nixos-unstable` input is not itself reproducible; pinning the exact input is the key property. Switching to Guix is an optional alternative, not a logical consequence of using Nix.

## Canonical comparison modules actually present

- `Exotic/ERL/Exploration/DMCPDistribution.agda`
- `Exotic/ERL/Exploration/MR15Reachability.agda`
- `Exotic/ERL/Exploration/OpenESDyadic.agda`
- `Exotic/ERL/Stages/Stage02_CHAD.agda`
- `Exotic/ERL/Stages/Stage03_LinearLearner.agda`
- `Exotic/ERL/Stages/Stage05_Representation.agda`
- `Exotic/ERL/Stages/Stage06_CoupledLearner.agda`

## Replication order

1. replace same-noise exponent repetition by independent finite noise or direct one-shot mutation;
2. prove exact `Fin 256` support/gcd reachability;
3. prove iid product factorization and exact finite expectation;
4. prove histogram rank consistency and exact closure;
5. prove full learner+EA irreducibility;
6. use the actual full-state self-loop theorem to conclude period 1;
7. extend exact VJP/CHAD through the actual forward path;
8. generate criterion-specific distribution theorems automatically;
9. keep CI manifest paths synchronized with real files;
10. promote only modules that are present and `--safe` checked into canonical status.

## Next replication prompt

Continue from the live `JohnChristianD/Actions` repository. Treat `.ci/canonical-module.txt` plus `.github/workflows/agda.yml` as the current CI authority, and treat the v147 theorem list in `Agda/README.md` as a closure target.

Repair MR15 mutation semantics with an explicit independent finite noise tape or equivalent one-shot mutation. Prove the actual `Fin 256` generator/gcd theorem. Formalize iid product weights and exact expectation from finite dyadic masses using small first-principles imports. Prove exact histogram rank consistency and sorting requirements. Prove full composed learner+EA irreducibility before invoking the causal-free self-loop theorem for period 1.

Extend CHAD/VJP through every actual representation primitive and keep GateNN diagonal theorems distinct from softsign theorems.

Make the Haskell conjecture generator grammar parameterized by distribution, mutation law, algebraic invariant, and statistical criterion. Emit candidate Agda propositions and accept only survivors checked with `agda --safe`. Use iterative CHAD only to help generate/rank differential conjectures.

Finally compare `D_tri`, flat, center-heavy, lazy-unit, Rademacher, and even-step laws through exact criterion-specific theorems. Do not assert a universal statistically best distribution. The algebraically defensible superiority class is criterion-conditioned extremality over a formally declared finite admissible set.
