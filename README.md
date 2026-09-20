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
- orbit-observation separation as an explicit contract;
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

The bounded exact-UAP surface includes exact retraction, decoder-transport, and postcomposition. The minimal bounded theorem needs a left inverse for exact readout. The standalone universal certificate exposes continuous left-invertibility, explicit orbit-observation separation, and exact readout for every target; separation is derived from the left inverse, so it is a visible redundant contract rather than an extra mathematical assumption.


## Terminology boundary

The active proof model is ordinary reinforcement learning (RL). The legacy filesystem/module namespace `Exotic/ERL/FullCoupled/...` is retained only to avoid a broad path-and-module migration in the proof surface; the mathematics and documentation do not claim an evolutionary-RL mechanism.


## Reservoir-computing universality boundary

The reservoir-computing literature uses a different universality problem from this finite exact RL algebra. Sugiura, Ariizumi, Asai, and Azuma (Mathematics 2025, 13, 3440) prove, under their continuous-time RC assumptions, that universality, the neighborhood separation property, and existence of a uniformly continuous left inverse are equivalent. They also prove that a universal reservoir functional has dense discontinuity points. Their earlier 2024 construction shows that a universal reservoir with finite-dimensional output can exist, including a single-output construction, so the result is not an 'infinite width' theorem. [Source: the 2025 paper and its 2024 predecessor.]

The present Agda result is different and exact. On the canonical Nat-indexed orbit, state equality implies index equality, while an `Int8` observation has only finitely many values. Therefore a global exact left inverse `inverse ∘ observe = id` is impossible on the whole orbit by pigeonhole. The theorem `canonicalNoGlobalInt8ContinuousLeftInverseOnDiscreteTopologies` strengthens the boundary by explicitly granting continuity under the discrete topologies: even then the finite observation cannot have a global exact left inverse.

Consequently:

`finite Int8 observation + infinite canonical orbit -> no global exact left inverse`

This is a cardinality contradiction, not a claim that chaotic reservoirs are required in every universal-approximation setting. The reservoir result explains the dense-discontinuity phenomenon in the continuous infinite-precision regime; the Agda theorem establishes the stricter finite-precision obstruction for this algebra.

## Equality-saturation e-graph boundary

The Mercury implementation now contains the standard equality-saturation stages that were previously missing from the repository-specific congruence structure: e-matching, rewrite application, repeated saturation to a fixed point or iteration cap, rebuilding/congruence maintenance, e-class analysis, and cost-guided extraction. The theorem-sync gate exercises the same pipeline against the source-derived semantic manifest. It does not make Mercury a proof authority: Agda `--safe` remains authoritative.


## Topology, import, and reservoir-universality boundary

The topology statement did not require a heavyweight topology package. The canonical learner monolith defines a minimal `Topology` record directly, using only the existing `Data.Empty` (`⊥`), `Data.Unit` (`⊤`), and `Data.Product` (`Σ`, `×`) primitives. `Continuous` is an explicit property over those topologies. The discrete topology is now also instantiated explicitly; under it every function is continuous, which makes the finite-observation contradiction independent of any continuity failure.

The import history is intentionally minimal. The canonical theorem monolith needs `Data.List` because its learner-replacement theorem surface uses `List`; the learner monolith does not currently use `List` and no longer imports it merely for symmetry. `Data.List.Sort` is not part of the current canonical proof lineage, and the older ordered-algebra work used custom `_≤_`/`_<` relation fields rather than a `Data.List.Sort` dependency. Those older ordered structures are not silently required by the exact-UAP proof.

The 2025 reservoir-computing result by Sugiura, Ariizumi, Asai, and Azuma proves equivalence, under its reservoir-computing assumptions, between universality, the neighborhood separation property, and a uniformly continuous left inverse, and proves dense discontinuity points for universal reservoirs. The authors connect this sensitivity to chaotic reservoirs, but that last step is presented as an implication/interpretation supported by cited chaotic-reservoir studies, not as a theorem that every universal system is chaotic. The 2024 study also constructs a universal reservoir with a single output, so infinite output width is not required.

A useful algebraic comparison is therefore a conditional resolution-versus-instability tradeoff, not a proved duality: rich input classes require enough distinguishability either through representational capacity/precision or through highly sensitive/discontinuous reservoir maps. This should not be conflated with sample complexity. Universality is an expressivity/property-of-a-function-space statement and does not by itself imply that training requires literally infinite data.

For this repository's exact finite algebra the stronger obstruction is cardinality. The canonical orbit is injectively indexed by `Nat`, while `Int8` has only 256 values. Hence a global exact observation left inverse is impossible. Granting both observation and inverse continuity under the explicit discrete topology does not change that result. Chaotic internal dynamics also cannot evade the theorem while the exact observation remains `Int8`: the final observation map still has finite codomain.

## Mercury proof-source synchronization

Mercury semantic extraction now checks that `Exotic/ERL/FullCoupled/TheoremsMonolith.agda` explicitly declares `{-# OPTIONS --safe #-}` before generating the semantic manifest. The theorem e-graph then consumes that source-derived manifest and exercises e-matching, rewrite application, saturation, rebuild, e-class analysis, and cost-guided extraction. Agda remains the proof authority; Mercury is the semantic synchronization/equality-saturation verification layer.
