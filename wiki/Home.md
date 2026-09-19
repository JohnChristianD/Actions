# Canonical Proof Wiki

This repository-side wiki source records the connected Guix, Agda, and Mercury architecture.

## Fix strategies

### Guix bootstrap

**Failure mode:** Guix-native Git could fail before repository checkout while building a pinned Git dependency.

**Fix:** keep Git outside the pure proof manifest. Container-native Git performs source and Guix-channel transport, then CI enters the pinned pure environment.

**Failure mode:** the stripped container lacked service names for HTTPS and Git.

**Fix:** initialize the minimal `http`, `https`, and `git` entries in `/etc/services` before networked Guix operations.

**Failure mode:** Savannah transport could be flaky, while shallow or blobless channel clones left `guix time-machine` without required Git objects.

**Fix:** use the verified GitHub mirror `neuroradiology/guix-mirror` as transport, assert the exact pinned commit, and keep a complete `version-1.5.0` single-branch history with blobs.

Pinned Guix commit:

`ac03c482b1910a1672427beaea07ddcd1d652806`

### Agda `--safe` + stdlib

The Agda lane uses the Guix-installed compiler with `--safe`.

The first focused compilation is a stdlib-import smoke test. The canonical learner, theorem monolith, focused tests, and generated theorem projections are then compiled using the same executable.

Agda is the proof acceptance boundary.

### Connected composed theorem

The main composed theorem is:

`canonical-endogenous-minimax-bellman-shapley-uap-theorem`

It combines:

- target semantics for the executable biased Watkins / negative q-Munchausen / F4-L2 path;
- an explicit minimax/Bellman-Shapley inclusion class;
- endogenous left-inverse factorization;
- exact discrete UAP;
- recurrent target-stream scan correctness;
- continuous-left-inverse readout transfer;
- bounded exact approximation/readout from the continuous left inverse;
- explicit orbit/ring-state injectivity and separation contracts;
- the Nat-clock pigeonhole contradiction;
- global exact `Int8` UAP impossibility on the infinite orbit.

The bounded result is genuinely finite. Its domain is `Fin bound`, and exact equality is the approximation relation. Infinitude is not an ingredient of this theorem.

### Mercury e-graph

The discovery chain is:

`learner_semantic_extractor.m`

-> `learner_semantic_manifest.m`

-> `interpolated_theorem_egraph.m`

-> `novel_learner_theorem_discovery.m`

The forced target is the composed Agda theorem:

`TheoremsMonolith.agda#canonical-endogenous-minimax-bellman-shapley-uap-theorem`

Mercury derives its semantic vocabulary from the canonical learner and theorem monoliths. The e-graph normalizes proof plans, including associative equality-composition structure.

The quotient is a discovery artifact, not an independent proof. Agda `--safe` remains authoritative.

## Representation-analysis hypotheses

The unigram, bigram, and onion hypotheses are preserved as empirical research questions rather than inserted into the formal proof surface.

### Hypothesis 1: unigram variables

The hypothesis tests whether each sequence position occupies a separate linear subspace of the final hidden state. A learned rotation and assignment matrix are used to define position-specific interchange interventions.

Formal boundary: a left-invertible observation gives exact readout and injectivity theorems. That does not establish the empirical existence of unigram subspaces in a trained GRU.

### Hypothesis 2: bigram variables

The hypothesis assigns representation to adjacent token pairs. A token intervention therefore affects the neighboring bigram variables as well.

Formal boundary: executable compositional equalities may be proved about the canonical learner, but representation labels remain empirical without intervention evidence.

### Hypothesis 3: onion representations

The hypothesis uses shared directions with different scales and autoregressive feedback to peel the dominant scale before decoding the next stored token.

Formal boundary: the canonical recurrent scan theorem proves the implemented recurrence's exact prefix semantics. It does not establish that the trained representation empirically realizes the onion mechanism.

## Authority map

| Layer | Authority |
|---|---|
| Guix bootstrap | Reproducible transport into the pinned toolchain |
| Guix manifest | Agda, stdlib, Mercury, Guile tool surface |
| Canonical learner monolith | Executable learner semantics |
| Theorem monolith | Connected formal composition |
| Mercury extractor | Source-derived semantic vocabulary |
| Mercury e-graph | Discovery and proof-plan quotienting |
| Generated Agda module | Source-owned theorem projections |
| Agda `--safe` | Final proof acceptance |
| Representation hypotheses | Empirical questions, not proofs |

## Guardrails

The canonical surface intentionally avoids a general topology hierarchy, Sion's theorem, generic strong-convexity/coercivity machinery for modular `Int8` updates, and reservoir literature.

Conditional mathematics is expressed with explicit premises. Global exact claims that contradict finite `Int8` observation are represented as impossibility results instead of being silently weakened.
