# Agda SMT automation and Vehicle boundary - 2026-09-30

## Scope

This note defines the interoperability boundary for external SMT assistance and Vehicle-derived formalisation. The tracked Agda source surface is strictly two monoliths: `CanonicalLearnerMonolith.agda` and `TheoremsMonolith.agda`.

## Schmitty

Schmitty v1.0.1 supplies Agda SMT reflection and a Z3 backend. Its upstream examples use `{-# OPTIONS --allow-exec #-}` and `solveZ3`. The theorem monolith uses `--allow-exec` for the direct Schmitty/Vehicle integration boundary. Schmitty remains automation assistance rather than a replacement proof kernel: a `solveZ3` result is accepted only after Agda checks the resulting theorem term.
Mercury graph topology continues to derive from `TheoremsMonolith.agda`. Schmitty can discharge suitable algebraic subgoals, and Vehicle can add/check a compatible specification interface, but neither creates graph edges or theorem nodes by conceptual similarity.

The graph gate remains:
- real Agda dependency edges only;
- A* cost guides traversal, never equality;
- emergent-composition reporting cannot promote unproved external statements;
- review frontier remains source-derived.

## Verification boundary

Schmitty is installed on the the same official Agda 2.8.0 toolchain used by the canonical workflow, and the theorem monolith consumes its Int/Z3 import surface directly. Vehicle's current Agda reflection interface is likewise imported by the theorem monolith from the pinned Vehicle source tree; no third tracked Agda source is introduced. The theorem lane uses the current integration flags rather than a second Agda version:

```sh
$AGDA_COMMAND --allow-exec -l standard-library -i . -i "$VEHICLE_AGDA_SOURCE" -i "$SCHMITTY_AGDA_SOURCE" -i "$AGDARSEC_AGDA_SOURCE" Exotic/ERL/FullCoupled/TheoremsMonolith.agda
```

The Pages surface remains independent of the Mirth synchronizer, but the Mirth C99 path itself is supported for the fast-dirty integration lane. nixpkgs exposes the `mirthc` executable and documents that Mirth compiles to C99; the branch uses `mirthc` -> C99 -> the Nix C compiler -> native synchronizer execution.

Stale when: Schmitty release, Z3 setup action, canonical Agda/std-lib versions, Vehicle Agda-library dependency, or theorem-graph authority changes.


## Tail-stability and convergence boundary

The repository now exposes a reusable `GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem`. Its premises are exact feature-step conjugacy, feature-tail stability, and GRU/feature injectivity; its conclusion is eventual state stationarity together with identifiability through the same injective encoding. This is the generic convergence kernel that Mercury should discover and that Schmitty/Vehicle may help discharge at their respective automation/specification boundaries.

Nash existence closes a different obligation: existence of an equilibrium in the specified finite strategic game, using mixed strategies. It does not identify that game's fixed-point correspondence with the GRU/MARL/physics/economic operator automatically. The composite theorem can therefore be witness-light only after the graph-selected operator identity, exact state transport, exact step conjugacy, tail-stability fact, and economic interpretation have been independently established; graph search and automation cannot manufacture a missing semantic correspondence.

The current `NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem` packages the GRU injectivity, MARL semantics, Hodge-Maxwell representation, four-law witness, and exact iterate transport, but its semantic closure witness `B` is still an explicit premise. The current `StationaryLimitTheorem` likewise requires transition law, convergence, and preservation of the limiting point. Therefore the remaining gap is not GRU injectivity or tail stability; it is the explicit identification of the Nash/economic fixed-point operator with the transported learner/physics operator and the corresponding interpretation witness.
