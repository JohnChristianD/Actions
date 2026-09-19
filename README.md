# Actions

The canonical proof architecture is intentionally narrow: one learner monolith, one theorem monolith, Mercury-only semantic e-graph discovery, and Guix-native orchestration.

## Canonical monoliths

Learner:

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

Theorem:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

The theorem monolith imports the canonical learner monolith as its only repository-local semantic source. Generalized learners, benchmark ports, and auxiliary theorem modules are not part of the canonical Agda safe lane.

## Exact target theorem

The learner defines an executable biased Watkins target with negative finite q-Munchausen bias, discounted critic maximum, and endogenous feedback. The theorem monolith proves the exact decomposition and exact F4/L2 consumption path.

`canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class` proves pointwise-envelope transport through an explicitly supplied monotone minimax/Bellman-Shapley operator.

No topology, interval-analysis package, or generic ordered-ring hierarchy is imported into the canonical theorem surface.

## Strong combined theorem

`canonical-endogenous-minimax-bellman-shapley-uap-theorem` composes:

- exact target semantics;
- minimax/Bellman-Shapley inclusion;
- endogenous left-inverse factorization;
- continuous-left-inverse readout transfer as an explicit premise;
- Nat-clock orbit injectivity;
- ring-state injectivity contract;
- dense-neighborhood separation contract;
- finite-Int8 pigeonhole contradiction.

This is a provable transfer schema under the explicit continuity/algebraic premises, not a claim that the current strict imports magically provide a topological universal-approximation library.

## Mercury discovery

The active discovery chain is:

`learner_semantic_extractor.m` -> `learner_semantic_manifest.m` -> `interpolated_theorem_egraph.m` -> `novel_learner_theorem_discovery.m`

The discovery gate forces:

`TheoremsMonolith.agda#canonical-endogenous-minimax-bellman-shapley-uap-theorem`

The generic e-graph handles source-derived proof-plan quotienting. Agda `--safe` is the proof acceptance boundary.

## Guix policy

The Guix driver has four lanes:

`agda-safe`, `mercury`, `discovery`, and `surface`.

The safe lane checks only the canonical monoliths and focused theorem/discovery tests.

The surface lane rejects Python, JVM-language, JavaScript/TypeScript, C/C++, .NET, HTML/CSS, TeX/LaTeX, shell-script, SSH/SCP, command-script, and non-README Markdown paths.

No unrelated web, database, typography, or alternate-language dependency is introduced into the strict Agda/Mercury/Guix proof path.
