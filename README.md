# Actions — Exact Recurrent Learner and Theorem-Graph Monograph

This repository formalizes a bounded recurrent learner, exact sequence-model semantics, finite-observation information boundaries, optimizer composition, and theorem discovery. The executable learner and theorem surface are separate: Agda is the proof authority; Mercury extracts semantic laws and searches dependency paths; Dhall declares the CI contract; Nix provides reproducible build composition.

The governing rule is: a graph candidate is not a theorem. A candidate must be reachable from declared semantic laws and then accepted by the Agda type checker. A* and e-graphs guide discovery and extraction; they do not replace proof.

## What each language does

**Agda — semantic and proof authority.** The canonical learner semantics live in `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`; the active theorem surface lives in `TheoremsMonolith.agda`. Agda's dependent type theory makes propositions and proofs part of the same typed language. With `--safe`, Agda disables postulates, unfinished proofs, unchecked termination, unsafe positivity/universe options, and other features that could undermine consistency. citeturn1search0turn1search2

**Mercury — graph-search and semantic extraction engine.** The `.ci/discovery/*.m` programs extract named semantic laws, represent dependency edges, run deterministic/semideterministic searches, build e-graph candidates, and use A*-style cost guidance. Mercury's type, mode, and determinism declarations are compiler-checked; its formal semantics require legal programs to satisfy those declarations. citeturn0search3turn0search0turn0search6

**Dhall — declarative CI policy.** `.ci/actions_ci.dhall` is not the theorem prover. It describes which verification lanes, commands, and graph gates CI should run. Dhall is total and strongly typed, with evaluation that terminates for well-typed expressions and no arbitrary general-purpose side effects. That makes it useful for expressing a machine-checkable automation policy without turning the policy language into another general-purpose execution authority. citeturn0search2turn0search9

**Nix — reproducibility and environment composition.** Nix supplies the reproducible package/build layer around the language toolchains and checks. It should be viewed as build-environment authority, not mathematical proof authority and not the theorem-discovery engine.

**GitHub Actions — execution substrate, not a proof language.** GitHub Actions runs the declared CI workflows in response to repository events. It can build and test the project, but a green workflow only means the configured checks passed; it does not make an unproved Agda proposition true. citeturn1search3turn1search8

### What “CI declaration” means

“CI declaration” means the **Dhall description of the verification pipeline**: the set of lanes, commands, gates, and orchestration rules that CI is supposed to execute. It is a declarative specification of *what must be checked*, while GitHub Actions is the mechanism that actually schedules/runs those checks.

In this repository the distinction is:

```
Dhall
  │ declares verification lanes and gates
  ▼
GitHub Actions / runner
  │ executes the declared checks
  ▼
Nix
  │ supplies reproducible tool/build environment
  ▼
Agda + Mercury + auxiliary checks
  │
  ├── Agda: proves/checks theorem statements
  └── Mercury: extracts/searches theorem dependencies
```

The important asymmetry is deliberate: **Dhall can say that Agda must pass; Dhall cannot prove the Agda theorem.**

## The Agda theorem relationship

The canonical dependency architecture is:

```
                         ┌──────────────────────────────┐
                         │ CanonicalLearnerMonolith.agda│
                         │ executable/state semantics   │
                         └──────────────┬───────────────┘
                                        │
                                        ▼
                         ┌──────────────────────────────┐
                         │ TheoremsMonolith.agda        │
                         │ exact theorem declarations   │
                         └──────────────┬───────────────┘
                                        │
                         Agda --safe    │ proof/type authority
                                        ▼
                 ┌──────────────────────────────────────────┐
                 │ learner_semantic_extractor               │
                 │ semantic-law extraction                   │
                 └──────────────────┬───────────────────────┘
                                    │
                                    ▼
                 ┌──────────────────────────────────────────┐
                 │ theorem_graph_search.m                   │
                 │ dependency search + A* + emergent paths │
                 └──────────────────┬───────────────────────┘
                                    │
                                    ▼
                 ┌──────────────────────────────────────────┐
                 │ theorem_monolith_egraph_sync.m           │
                 │ equality saturation + extraction gates   │
                 └──────────────────┬───────────────────────┘
                                    │
                                    ▼
                         ┌──────────────────────┐
                         │ Dhall CI declaration │
                         │ verification policy  │
                         └──────────┬───────────┘
                                    │
                                    ▼
                         GitHub Actions / Nix
                         execute the checks
```

The arrow direction here is intentionally not “proof flows upward.” **Agda establishes the propositions; the discovery machinery reads those established declarations and searches for compositions.** A graph path discovered by Mercury/e-graphs still needs an Agda statement before it becomes proof.

## The current emergent endogenous result

The newest cross-domain endogenous composition is:

```
CanonicalExactRNNLMTheorem
        │
        ├── global token-LM composition
        ├── architecture-preserving transport
        │
        ▼
CanonicalExactRNNLMObservationTopologyCapabilityTheorem
        │
        ├── endogenous observation boundary
        ├── endogenous topology boundary
        └── finite-information boundary
        │
        ▼
CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
        ▲
        │
        ├── finite POMDP probability semantics
        └── exact belief-update transport
```

This is an **emergent composition theorem**, not a new primitive axiom. Its novelty is in the dependency closure exposed by the graph: an exact RNN-LM capability surface is now connected to the endogenous finite-observation/topology boundary and to finite POMDP probability/belief transport.

## Theorem: how much vocabulary can this formulation store?

For the particular canonical formulation, the answer is exact:

```
CanonicalToken
    ≡ Fin 256
    ≡ Int8

therefore:

    |CanonicalToken| = 256
```

The monolith defines `CanonicalToken = Fin 256`, and the encode/decode functions are exact inverses against `Int8`. Therefore this formulation has **256 distinct canonical token symbols** in its formal vocabulary.

That is a theorem about this formal carrier, not about arbitrary language models. It also does **not** mean the model can only represent 256 different sequences: the sequence type is `List CanonicalToken`, so there are arbitrarily long finite sequences over the 256-symbol alphabet. The vocabulary bound is 256 symbols; sequence-space cardinality is a different question.

The current `CanonicalTokenVocabularyUpperBoundTheorem` expresses the exact carrier equivalence. It should not be described as a statistical estimate or as a bound on real-world LLM vocabularies.

## Formal perspectives

The learner has several deliberately separated mathematical readings.

- **Continual/online learning:** explicit recurrent state, policy readout, optimizer state, and information-retaining/lossy observations.
- **Informatics:** recurrent prefixes induce endomorphisms; composition gives the recurrent prefix monoid.
- **Dynamical systems:** exact clock growth, cycle exclusion, conjugacy, finite-factor recurrence, and observation boundaries.
- **Stochastic semantics:** exact finite probability masses, finite POMDP kernels, and belief-update transport.
- **Theoretical computer science:** finite-carrier pigeonhole boundaries and the explicitly specified exact-computability contract.
- **RNN-LM semantics:** finite token carrier, recurrent token processing, logit traces, sparsemax surfaces, token-LM composition, and architecture-preserving transport.

These are formal structural correspondences. They are not claims that the learner is an empirical state-of-the-art language model, a physical system, a biological model, or a general equilibrium theorem.

## Safety and suitability of the language stack for autonomous agents

There is no defensible literature-wide theorem saying that these are the “safest languages overall” for autonomous agents. Safety is role-dependent.

For **proof authority**, Agda's `--safe` mode is unusually strong because it explicitly rejects several mechanisms that can undermine consistency, including postulates, unfinished metas, unchecked termination, unsafe positivity, and inconsistent universe options. citeturn1search0turn1search2

For **search/orchestration logic**, Mercury has a strong static contract around types, modes, and determinism, and its declarative semantics are explicitly specified. That is valuable for autonomous graph search because incorrect data-flow or solution-count assumptions can become compiler errors rather than comments. citeturn0search3turn0search0turn0search6

For **configuration policy**, Dhall has an especially relevant safety profile: it is total rather than Turing-complete, and its type system rules out classes of evaluation failures before configuration is consumed. citeturn0search2

Nix is valuable primarily for reproducibility and isolation of the build environment; GitHub Actions is the execution substrate. Neither should be mistaken for a proof system.

So the strongest accurate claim is not “best out of every language.” It is: **the stack gives different layers different safety contracts, with Agda holding semantic proof authority, Mercury constraining search behavior, Dhall constraining configuration evaluation, and Nix constraining environment construction.** That separation is more important than declaring a universal winner.

## Exactness policy

The repository should not obtain a green result by weakening a theorem, replacing a missing proof with `⊤`, silently changing a carrier, or treating an e-graph extraction as proof. Likewise, the POMDP probability seam is a finite exact semantics layer, not a claim of full measure-theoretic probability, and the RNN-LM surface is a formal capability boundary, not a benchmark result.

The graph-search system can discover compositions of declared laws. Agda remains responsible for establishing the resulting proposition.

## Status

The canonical proof surface is:

- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`
- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

The discovery surface is:

- `.ci/discovery/learner_semantic_extractor.m`
- `.ci/discovery/theorem_graph_search.m`
- `.ci/discovery/theorem_monolith_egraph_sync.m`

The automation/build surfaces are:

- `.ci/actions_ci.dhall`
- Nix configuration and package/build definitions
- GitHub Actions workflows

The intended workflow is therefore:

```
declare exact law
      ↓
prove/type-check in Agda
      ↓
extract semantic law
      ↓
search dependency graph
      ↓
e-graph/A* candidate extraction
      ↓
promote only when Agda proves the composed theorem
      ↓
CI executes the declared verification contract
```

This keeps the mathematical authority, discovery machinery, and automation machinery distinct while allowing them to cooperate.
