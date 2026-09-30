# Actions

This repository is a mechanically checked Agda system for a coupled recurrent learner and its explicit semantic boundaries.

The authority order is:

1. Agda definitions and proofs.
2. Mercury declaration discovery and semantic graph search.
3. Dhall verification contracts.
4. Nix environment composition.
5. Mirth/C99 synchronization checks.
6. Pure Elm presentation for GitHub Pages.

No graph edge, generated report, solver answer, model weight, or UI artifact is promoted to proof authority.

## Proof surface

Exactly two tracked Agda modules are authoritative:

- `Exotic/FullCoupled/CanonicalLearnerMonolith.agda`
- `Exotic/FullCoupled/TheoremsMonolith.agda`

The theorem monolith directly consumes the pinned Schmitty and Vehicle Agda interfaces. Schmitty supplies SMT/Z3 automation. Vehicle supplies its Agda reflection/interface boundary. Neither library becomes a second semantic authority.

The generic convergence kernel is:

```
injective encoding
    +
exact step conjugacy
    +
eventually fixed feature tail
    |
    v
tail-fixed source state
    +
eventual stationarity
    +
identifiability
```

The kernel does not manufacture economic, physical, or game-theoretic witnesses.

## Baird seven-state boundary

The theorem monolith now contains an explicit `bairdSevenStar` boundary package.

It records the standard seven-state, eight-feature setup:

- six upper states and one lower state;
- dashed behavior probability 6/7;
- solid behavior probability 1/7;
- target policy always solid;
- zero reward;
- discount factor 0.99;
- upper-state representation `2*w_i + w_8`;
- lower-state representation `w_7 + 2*w_8`.

The actual numerical divergence result remains an explicit `BairdSevenStarDivergenceWitness`. This is deliberate: literature claims and empirical runs are not silently converted into Agda axioms.

The Baird boundary is separate from the GRU tail-stability theorem. It belongs to the off-policy temporal-difference/function-approximation stability boundary.

## Toolchain

The GitHub Actions Agda lanes use the first-party `agda/agda-setup-action@v1` with Agda 2.8.0 and agda-stdlib 2.3.

The repository previously used the legacy `wenkokke/setup-agda` action. It is no longer used by the main verification lanes.

Vehicle is pinned to a source revision and checked at its Agda interface boundary. A standalone Vehicle compiler build is not part of the proof authority.

Nix does not replace C99. The synchronization chain is:

```
Mirth source
    |
    v
mirthc
    |
    v
C99 source
    |
    v
cc
    |
    v
executable
```

Nix packages and pins that toolchain.

## Mirth synchronization

The tracked Mirth sources are:

- `.ci/mirth/agda_to_elm.mth`
- `.ci/mirth/ascii_surface.mth`

The first emits the fixed two-module Elm presentation surface. The second compiles to C99 and checks every tracked Markdown and Elm source for ASCII-only content.

The CI lane also verifies the README documentation index. There is no ML-generated source rewrite in this path.

Gemma weights, Bonsai.ML artifacts, and other opaque model checkpoints are not vendored or used as proof inputs. An ML workload may consume explicit interfaces, but it cannot silently become the canonical semantic definition.

## GitHub Pages

`site/Main.elm` is the presentation program. It remains pure Elm.

Mermaid is not embedded into the Elm application and is not a runtime dependency. The Pages application therefore remains an Elm-only program.

Project site:

https://johnchristiand.github.io/Actions/

## Repository contracts

The main checks cover:

- canonical Agda learner safety;
- theorem-monolith checking with Schmitty and Vehicle interfaces;
- Baird counterexample boundary registration;
- Mercury theorem/e-graph discovery;
- Mirth C99 synchronization;
- Markdown/Elm ASCII synchronization;
- pure Elm site compilation;
- static Pages verification;
- pinned Nix composition.

The current tracked proof surface is intentionally limited to the two Agda monoliths. Superseded theorem/source snapshots are not restored.

<!-- BEGIN GENERATED DOCUMENTATION INDEX -->

Generated from the current tracked Markdown surface.

### Research

- [Agda proof search in this repository](docs/research/agda-auto-proof-search.md)
- [Agda SMT automation and Vehicle boundary - 2026-09-30](docs/research/agda-smt-vehicle-boundary-2026-09-30.md)

<!-- END GENERATED DOCUMENTATION INDEX -->
