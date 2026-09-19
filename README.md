# Actions

This repository keeps one canonical semantic learner, one canonical theorem monolith, Mercury-only semantic e-graph discovery, and a Guix-connected proof pipeline.

## Canonical proof surface

The learner source is:

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

The theorem source is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

The theorem monolith imports the learner monolith as its only repository-local semantic source. The canonical Agda lane uses `{-# OPTIONS --safe #-}`.

Guix installs Agda and the Agda standard library. The safe lane first compiles a focused stdlib-import test, then compiles the canonical learner, theorem monolith, focused tests, and generated theorem projections with the same Guix-installed `agda --safe` executable.

## Guix bootstrap fix strategy

CI separates transport/bootstrap from the pinned pure proof environment.

1. Container-native Git performs source checkout. Git is deliberately absent from the pure Guix proof manifest.
2. The container initializes the minimal `http`, `https`, and `git` entries in `/etc/services` before networked Guix work.
3. The pinned Guix channel is fetched with container-native Git from a verified GitHub mirror and checked against the exact commit `ac03c482b1910a1672427beaea07ddcd1d652806`.
4. The channel is cloned as complete `version-1.5.0` history and blobs so `guix time-machine` can resolve every referenced Git object.
5. Only then does CI enter the pure manifest containing Agda, Agda stdlib, Mercury, and Guile.

This prevents network/bootstrap failures from masquerading as proof failures while retaining the exact Guix pin.

## Connected composed Agda theorem

The main composed theorem is:

`canonical-endogenous-minimax-bellman-shapley-uap-theorem`

It combines:

- exact biased Watkins, negative q-Munchausen, and F4-L2 target semantics;
- an explicitly supplied monotone minimax/Bellman-Shapley inclusion class;
- endogenous left-inverse factorization;
- exact discrete UAP from a left inverse;
- exact recurrent scan semantics for the endogenous target stream;
- continuous-left-inverse readout transfer as an explicit premise;
- **bounded exact approximation/readout from that continuous left inverse**;
- orbit/ring-state injectivity and the explicit separation contract;
- the Nat-clock pigeonhole contradiction;
- impossibility of a global exact `Int8` UAP over the unbounded canonical orbit.

The bounded theorem is finite by construction: its domain is indexed by `Fin bound`, and exact equality is the approximation relation. It needs no infinite orbit, metric, limit, compactness, or topology package.

The continuous layer remains explicit through:

`ContinuousLeftInverseTheorem State Feature observe inverse Continuous`

No hidden topology is introduced into the strict import boundary.

The exact discrete universal statement has the clean constructive form: universal exact readout for every target factors through an observation exactly when that observation has a left inverse. Conversely, the infinite canonical orbit cannot have a global exact `Int8` observation with a left inverse, and the theorem surface explicitly proves that impossibility.

## Mercury semantic e-graph

Mercury owns semantic discovery and e-graph normalization:

`learner_semantic_extractor.m` -> `learner_semantic_manifest.m` -> `interpolated_theorem_egraph.m` -> `novel_learner_theorem_discovery.m`

The forced target is:

`TheoremsMonolith.agda#canonical-endogenous-minimax-bellman-shapley-uap-theorem`

The e-graph is a discovery and proof-plan normalization layer. Its associative proof-composition quotient is not the proof itself. Agda `--safe` remains the acceptance boundary.

Generated source-derived projections live in:

`Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda`

The generated module is also `--safe` and contains projections of source-owned theorems rather than a hard-coded theorem registry.

## Representation hypotheses: research boundary

The unigram, bigram, and onion hypotheses supplied for recurrent representation analysis are documented as empirical hypotheses, not silently promoted to formal facts about the canonical learner.

### Hypothesis 1: unigram variables

The hypothesis asks whether sequence positions occupy separate linear subspaces of the final hidden state. A rotated representation and assignment matrix identify candidate subspaces, and interchange interventions test whether replacing a position's subspace preserves exact target decoding.

Formal connection: an exact readout consequence follows constructively from a left-invertible observation. The Agda theorem does not assert that a trained GRU necessarily learns unigram subspaces.

### Hypothesis 2: bigram variables

The hypothesis assigns representation to adjacent token tuples, so an intervention around one token affects the neighboring bigram variables as well.

Formal connection: the theorem surface verifies executable compositional laws. It does not label the learner's hidden representation as bigram-based without experimental evidence.

### Hypothesis 3: onion representations

The hypothesis models multiple positions in a shared direction with different magnitudes and uses autoregressive feedback to peel the dominant layer before decoding the next one.

Formal connection: the recurrent scan theorem proves the executable recurrence's prefix semantics. It does not prove that the hidden representation empirically implements the onion mechanism.

The boundary is intentional:

**experimental representation** -> hypothesis and intervention target

**source-derived Agda equality** -> formal theorem

**Mercury e-graph** -> semantic discovery and proof-plan quotient

**Agda `--safe`** -> proof acceptance

## CI lanes

Guix runs four connected lanes:

`agda-safe`, `mercury`, `discovery`, and `surface`.

The Agda lane checks the canonical monoliths and focused tests with `agda --safe`.

The Mercury lanes compile and run only the canonical discovery sources.

The surface lane enforces the canonical source-language policy. Documentation Markdown is restricted to the root README and the controlled `wiki/` documentation tree.

## Deliberate mathematical boundary

The strict surface does not import a general topology hierarchy, Sion's minimax theorem, generic strong-convexity/coercivity machinery for modular `Int8` state updates, or reservoir literature.

Where a result is conditional, the condition is explicit. Where a global claim is impossible under finite `Int8` observation, the theorem says so rather than hiding the contradiction.
