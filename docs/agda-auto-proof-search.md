# Agda proof surface

## Authority

Exactly two Agda sources are active: `FullCoupled/CanonicalLearnerMonolith.agda` and `FullCoupled/TheoremsMonolith.agda`.

An accepted Agda term is authoritative. Mercury, Dhall, Mirth, Nix, SMT, Vehicle, JAX algorithm contracts, and Elm are supporting layers.

## GRU left inverse and injectivity

The canonical statistical observation contains the original `GRUState`; its decoder is first projection.

The accepted chain is `canonicalGRUStatisticalDecodeEncode` -> `canonicalGRUStatisticalEncodeLeftInverse` -> `leftInverse-implies-injective` -> `canonicalGRUStatisticalEncodeInjective`.

`CanonicalGRUStatisticalInjectivityTheorem` packages the result. It proves injectivity of the observation encoding, not injectivity of `gruStep`.

`GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem` composes that injectivity with exact step conjugacy and an eventually fixed feature tail. It yields tail-fixed source state, eventual stationarity, and identifiability.

## Finite mixed-Nash graph convergence

The theorem monolith now contains a finite-rank A* / e-graph convergence certificate plus an explicit Brouwer-to-Nash reduction.

The analytical existence seam is:

`BrouwerMixedNashExistence` -> `nashEveryFiniteGameViaBrouwer` -> `brouwerMixedNashFixedPointBridge`.

The graph composition seam is:

`finiteMixedNash-brouwer-egraph-astar-proof` -> `finiteMixedNash-egraph-astar-convergence` -> `finiteMixedNash-egraph-astar-eventualStationarity`.

The A* score orders dependency search. It is not semantic proof evidence. E-graph paths carry interpretation equality through `eGraph-path-sound` and `eGraphAStarConvergenceSemanticClosure`.

`finiteMixedNash-cycle-transport` transports the convergence certificate across an exact state isomorphism while reusing finite-cycle exclusion. `finiteMixedNash-from-GRU-tail` composes the same mixed-Nash predicate with the GRU injective tail-stability kernel.

The Agda code proves the reduction and all equality/convergence compositions. The Brouwer fixed-point theorem itself remains an explicit analytical witness in `BrouwerMixedNashExistence`; the repository does not silently postulate an implementation of Brouwer.

The final composed certificate is `finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof`. Its fields retain the Brouwer witness, finite-rank e-graph/A* witness, GRU injective tail witness, and a `StationaryLimitTheorem`. The projection `finiteMixedNash-brouwer-gru-egraph-astar-distribution-fixed` exposes the stationary distribution fixed point, while `finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof-nash` exposes the mixed-Nash existence witness. Mercury's review frontier now requires this composed path.

## Canonical Baird boundary

The active Baird construction is specialized to the already-tail-stable canonical learner. There is no generic Baird record.

`CanonicalLearnerBairdSevenStarWitness K s` carries the seven-state/eight-feature construction, 6/7 and 1/7 behavior, solid target, zero reward, 99/100 discount, upper/lower feature equations, the canonical persistent-GRU iterate tail, and an explicit divergence witness.

The tail field is exactly `canonicalPersistentGRU-afterFullStep-iterate K n s`. Baird is therefore downstream of the canonical learner proof rather than a generic state-transition schema.

## Retained sparsity theorems

L1 and 1-path-norm definitions, wrappers, and theorems are no longer active. They were not required by the canonical theorem obligations.

The retained hard-sparsity result is `CanonicalHardSparsityDegeneracyTheorem`, the exact zero-threshold equivalence between `HardSparse K s` and `SoftSparseBounded K s zero`.

The retained finite Tsallis-2 surface is `ActionWeights`, `actionSupportCount`, `actionWeightSum`, `actionWeightSquareSum`, `generalTsallis2Denominator`, `generalTsallis2Numerator`, `generalTsallis2NearSparsity`, its zero/nonzero-definition laws, `generalSupportSparsity`, and `UniformSupportTsallisBoundary`.

These are finite constructive definitions and equalities. Continuous Shannon or analytic regularity is not inferred.

## Physics, economics, and PPAD

Physics and economics remain active theorem families: Hodge-Maxwell/four-law interfaces, GRU/physics transport, production, demand/supply, excess demand, market-clearing and supporting-price witnesses, Walrasian interfaces, stationary/fixed-point closures, and economic composition.

No PPAD-completeness theorem is claimed. A genuine completeness proof requires an explicit polynomial-size total search relation, encoding-size bounds, membership, and a hardness reduction.

## JAX algorithm contracts

The repository no longer contains the Python JAX wrapper. The retained JAX-facing surface is `JAXExecutionMirrorReproof`.

Its finite Agda contracts cover vectorized affine mapping, associative prefix execution, recurrent scan, lexicographic ordering, sparse-support size/top-k/policy selection, integer LayerNorm, signed gating, scalar/batched GRU hidden updates, Tsallis-2 near-sparsity, support sparsity, and scan-sum.

The prefix and batched-GRU record fields are exact laws against their finite Agda implementations rather than tautological self-equalities. The contracts prove the finite algorithm semantics; they do not prove Python/JAX compiler behavior.

## Mirth synchronization and concurrency

The learner common-import block is the synchronization source of truth. The Mirth synchronizer checks marker cardinality, exact byte equality, dependency direction, canonical learner import count, and the retained Vehicle integration boundary.

Independent predicates run concurrently, every child status is collected, and the aggregate fails if any predicate fails. Write mode uses a bounded directory lock and replaces the theorem block only after a complete candidate has been constructed.

The Mirth graph program also runs independent learner/theorem extraction passes concurrently and emits deterministic nodes and edges. The graph is source-derived, not an Agda elaboration.

## Exhaustive Elm relation view

The generated Elm graph contains every declaration/reference edge produced by the source parser for the two active monoliths. The Pages UI exposes the complete generated edge list, declaration search, learner/theorem filtering, selected-node detail, incoming/outgoing relations, relation counts, and a dynamic SVG neighborhood.

This is Mermaid-like interaction implemented in pure Elm. No Mermaid runtime is required.

## Toolchain

The Nix flake pins the current nixpkgs revision and exposes one Agda wrapper containing `agdaPackages.agda` plus `agdaPackages.standard-library`. CI no longer installs a separate Agda action or external solver source tree.

Tracked Markdown is link-free.

## Agda proof-relevant unification

Both active monoliths use `--without-K`; the canonical learner also uses `--cubical=compatible`. Agda's production LHS unifier already uses its right-to-left strategy for indexed equations. There is no user CLI flag that separately selects that strategy.

Trace it directly:

```text
agda --safe --cubical=compatible -v tc.lhs.unify:40 FullCoupled/CanonicalLearnerMonolith.agda
```

The cubical-compatible branch can attempt the internal `LeftInverse` construction after a successful unification. Useful diagnostics:

```text
agda --safe --cubical=compatible \
  -v tc.lhs.unify:40 \
  -v tc.lhs.unify.inv:40 \
  -v tc.lhs.unify.inv.badstep:20 \
  FullCoupled/TheoremsMonolith.agda
```

`Agda.TypeChecking.Rules.LHS.Unify` and `Agda.TypeChecking.Rules.LHS.Unify.LeftInverse` are typechecker Haskell, not Agda modules to import.

## Meta-F*-style automation boundary

Keep exactly two Agda source files. Put repository-specific tactic code inside `TheoremsMonolith.agda` rather than adding a third module.

The minimal architecture is:

```text
goal
  -> Agda Reflection / TC
  -> inspect context and target
  -> normalize / specialize
  -> dependent proof search
  -> native Agda term
  -> native reflected solver / search leaf
  -> Agda checker
```

Use Agda's built-in Auto and Search About as existing interactive search. Add custom `TC` code only when a proof-state transformation is specific enough that a reusable tactic earns its maintenance cost.


## YAMLScript

The pinned nixpkgs revision already contains `pkgs.yamlscript` 0.3.0. It is exposed both in the dev shell and as a flake package named `yamlscript`.

Dev shell:

```text
nix develop .#default
ys --version
```

Global per-user Nix profile:

```text
nix profile install .#yamlscript
ys --version
```

This uses the repository's pinned nixpkgs package rather than a vendored YAMLScript build. Existing GitHub Actions workflow files remain YAML because GitHub's workflow loader consumes YAML; adding a YAMLScript generation layer there would be needless machinery.
