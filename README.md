# Actions

This repository keeps one canonical semantic learner, one canonical theorem monolith, Mercury-only semantic e-graph discovery, and a pinned Nix-connected proof pipeline.

## Canonical proof surface

The learner source is:

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

The only active theorem source is:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

That theorem monolith imports the learner monolith as its only repository-local semantic source and is checked with `{-# OPTIONS --safe #-}`.

There is no generated Agda theorem projection. Mercury synchronizes against the source-derived theorem monolith; Nix supplies the package environment, the NixOS-maintained installer action bootstraps Nix, and Agda performs the kernel check. One theorem source, because apparently software projects require ritual before they will stop duplicating themselves.

## Which tool owns the sync?

**Mercury owns e-graph sync and semantic discovery. Nix owns toolchain bootstrap and reproducible execution. Agda owns proof acceptance.**

The division is deliberately strict:

`CanonicalLearnerMonolith.agda` + `TheoremsMonolith.agda`
-> Mercury semantic extraction
-> Mercury semantic manifest
-> Mercury e-graph normalization
-> Mercury theorem-monolith sync gate
-> Nix-pinned `agda --safe`
-> kernel-checked theorem monolith

Mercury never writes a second Agda theorem file. The sync program is:

`.ci/discovery/theorem_monolith_egraph_sync.m`

The generic e-graph implementation remains:

`.ci/discovery/interpolated_theorem_egraph.m`

The e-graph is a discovery/proof-plan normalization layer, not a second proof authority.

## Nix toolchain strategy

CI installs Nix once and enters the repository flake. The flake pins nixpkgs, layers the upstream Agda 2.8.0 release, pins the Agda standard library at v2.4, and obtains Mercury 22.01.9 from nixpkgs. No Guix channel, Guile manifest, or Scheme CI driver is required.

The verification script runs Agda kernel checking, Mercury theorem verification, Mercury e-graph discovery, and the canonical source-policy surface audit from one Nix development shell.

## Infinite-state proof

The infinite-state argument is in the theorem monolith under:

`canonicalInfiniteStateOrbitEmbedding`

It proves the Nat-indexed canonical orbit is injective:

`C.iterateCanonical K m s ≡ C.iterateCanonical K n s -> m ≡ n`

The proof is constructive. It uses the exact clock-growth law

`C.clock (C.iterateCanonical K n s) ≡ C.clock s + n`

and Nat cancellation. There is also the no-global-exact-UAP route:

`canonicalPigeonholeNatClockContradiction`

and:

`canonicalNoGlobalInt8DiscreteUAPOnOrbit`

Those together make the boundary explicit: the canonical orbit is infinite in the Nat-indexed sense, while a single finite `Int8` observation cannot admit a global exact left inverse over that orbit.

## Exact bounded universal approximation through continuous left-injectivity

The strict theorem surface does not smuggle in a topology library. Continuity is an explicit predicate in:

`ContinuousLeftInverseTheorem State Feature observe inverse Continuous`

That witness supplies:

- continuous observation;
- continuous inverse;
- an exact left inverse;
- injectivity of the observation;
- exact readout transfer for arbitrary targets.

The finite exact-UAP consequence is:

`boundedUniversalExactApproximation-through-continuousLeftInverse`

Its domain is `Fin bound`. For every target `State -> Output` and every bounded index, the theorem gives exact equality:

`target (embed i) ≡ target (inverse (observe (embed i)))`

The underlying record is:

`BoundedContinuousLeftInverseExactApproximationTheorem`

and the implementation route is:

`boundedExactApproximation-on-boundedOrbit`

So this is an exact bounded universal readout theorem through a continuous left inverse, not a fabricated metric approximation theorem.

## Connected composed Agda theorem

The main composed theorem is:

`canonical-endogenous-minimax-bellman-shapley-uap-theorem`

It combines:

- exact biased Watkins, negative q-Munchausen, and F4-L2 target semantics;
- an explicitly supplied minimax/Bellman-Shapley inclusion class;
- endogenous left-inverse factorization;
- exact discrete UAP from a left inverse;
- exact recurrent scan semantics for the endogenous target stream;
- continuous-left-inverse readout transfer;
- **bounded exact universal approximation/readout from that continuous left inverse**;
- ring-state injectivity;
- the explicit **infinite-state orbit embedding**;
- dense-neighborhood separation as an explicit contract;
- the Nat-clock pigeonhole contradiction;
- impossibility of a global exact `Int8` UAP over the unbounded canonical orbit.

The constructor for the composed theorem directly includes the bounded theorem and infinite-state orbit proof, so the Mercury dependency graph can see those as connected source laws rather than decorative documentation. The minimal exact-universal-readout certificate exposes three facts directly: a continuous left inverse, explicit observation separation, and exact readout for every target. Separation is derived from the left-inverse witness, so the separated field is intentionally redundant but makes the proof contract visible.

## Mercury e-graph sync contract

The forced target is:

`TheoremsMonolith.agda#canonical-endogenous-minimax-bellman-shapley-uap-theorem`

The Mercury sync gate requires the target dependency set to contain the continuous-left-inverse transfer, bounded exact approximation, infinite-state orbit embedding, Nat-clock pigeonhole contradiction, and global-`Int8` UAP impossibility law.

The sync report records:

`single_agda_source = true`

`generated_agda_module = false`

`proof_authority = Agda --safe`

Agda is still the only component allowed to accept the theorem. Mercury can discover that the wires are connected; it cannot bless a bad proof. Civilization narrowly avoids another parser being mistaken for a kernel.

## Representation hypotheses: research boundary

The unigram, bigram, and onion hypotheses supplied for recurrent representation analysis remain empirical hypotheses, not formal facts about the canonical learner.

### Hypothesis 1: unigram variables

The hypothesis asks whether sequence positions occupy separate linear subspaces of the final hidden state. A rotated representation and assignment matrix identify candidate subspaces, and interchange interventions test whether replacing a position's subspace preserves exact target decoding.

Formal connection: an exact readout consequence follows constructively from a left-invertible observation. The Agda theorem does not assert that a trained GRU necessarily learns unigram subspaces.

### Hypothesis 2: bigram variables

The hypothesis assigns representation to adjacent token tuples, so an intervention around one token affects the neighboring bigram variables as well.

Formal connection: the theorem surface verifies executable compositional laws. It does not label the learner's hidden representation as bigram-based without intervention evidence.

### Hypothesis 3: onion representations

The hypothesis models multiple positions in a shared direction with different magnitudes and uses autoregressive feedback to peel the dominant layer before decoding the next one.

Formal connection: the recurrent scan theorem proves the executable recurrence's prefix semantics. It does not prove that the hidden representation empirically implements the onion mechanism.

The boundary remains:

**experimental representation** -> hypothesis and intervention target

**source-derived Agda equality** -> formal theorem

**Mercury e-graph** -> semantic discovery and proof-plan quotient

**Agda `--safe`** -> proof acceptance

## CI lanes

Nix runs four connected lanes:

`agda-safe`, `mercury`, `discovery`, and `surface`.

The Agda lane checks the canonical learner, the single theorem monolith, and focused tests with the same Nix-provided `agda --safe -l standard-library` executable.

The Mercury lane runs the theorem-monolith e-graph sync and the generic e-graph regressions. The sync program emits a report but does not generate Agda source.

The discovery lane runs the same source-derived semantic/e-graph chain.

The surface lane rejects noncanonical language/script files, rejects a second generated Agda theorem module, rejects a repository-side wiki tree, and requires the single active `TheoremsMonolith.agda`.

## Deliberate mathematical boundary

The strict surface does not import a general topology hierarchy, Sion's minimax theorem, generic strong-convexity/coercivity machinery for modular `Int8` state updates, or reservoir literature.

Where a result is conditional, the condition is explicit. Where a global claim is impossible under finite `Int8` observation, the theorem says so rather than hiding the contradiction.


## Agda proof lane update

The proof lane uses the repository flake for the pinned Nix package environment, while the official Agda setup action installs Agda 2.8.0.2 and standard-library 2.4. The GitHub runner installs Nix with the NixOS-maintained nix-installer action, pinned by commit, and the workflow pins Nix 2.35.1.

The bounded exact-UAP surface includes exact retraction, decoder-transport, and postcomposition. The minimal bounded theorem needs a left inverse for exact readout; continuity is represented as an explicit abstract predicate until an actual topology is imported, and dense-neighborhood separation is not a prerequisite for the bounded theorem.


## Terminology boundary

The active proof model is ordinary reinforcement learning (RL). The legacy filesystem/module namespace `Exotic/ERL/FullCoupled/...` is retained only to avoid a broad path-and-module migration in the proof surface; the mathematics and documentation do not claim an evolutionary-RL mechanism.
