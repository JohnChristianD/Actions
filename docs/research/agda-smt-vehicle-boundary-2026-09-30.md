# Agda SMT automation and Vehicle boundary — 2026-09-30

## Scope

This note defines the interoperability boundary for external SMT assistance and Vehicle-derived formalisation. The tracked Agda source surface is strictly two monoliths: `CanonicalLearnerMonolith.agda` and `TheoremsMonolith.agda`.

## Schmitty

Schmitty v1.0.1 supplies Agda SMT reflection and a Z3 backend. Its upstream examples use `{-# OPTIONS --allow-exec #-}` and `solveZ3`. This repository does not add those execution options to either canonical proof monolith; the Schmitty lane is non-authoritative installation/trust verification only.
Mercury graph topology continues to derive from `TheoremsMonolith.agda`. Schmitty is evidence-only automation. Vehicle remains an external compatibility candidate. Neither creates graph edges or theorem nodes by conceptual similarity.

The graph gate remains:
- real Agda dependency edges only;
- A* cost guides traversal, never equality;
- emergent-composition reporting cannot promote unproved external statements;
- review frontier remains source-derived.

## Verification boundary

Schmitty is installed on the same single latest Agda toolchain used by the canonical workflow, and the theorem monolith consumes its Int/Z3 import surface directly. Vehicle's current Agda reflection interface is likewise imported by the theorem monolith from the pinned Vehicle source tree; no third tracked Agda source is introduced. The theorem lane uses the current integration flags rather than a second Agda version:

```sh
$AGDA_COMMAND --allow-exec -l standard-library -i . -i "$VEHICLE_AGDA_SOURCE" -i "$SCHMITTY_AGDA_SOURCE" -i "$AGDARSEC_AGDA_SOURCE" Exotic/ERL/FullCoupled/TheoremsMonolith.agda
```

The Pages surface remains independent of the Mirth synchronizer, but the Mirth C99 path itself is supported for the fast-dirty integration lane. nixpkgs exposes the `mirthc` executable and documents that Mirth compiles to C99; the branch uses `mirthc` -> C99 -> the Nix C compiler -> native synchronizer execution.

Stale when: Schmitty release, Z3 setup action, canonical Agda/std-lib versions, Vehicle Agda-library dependency, or theorem-graph authority changes.


## Tail-stability and convergence boundary

The exact infinite stable tail is stronger than a generic convergence hypothesis for the affected representation. Once a representation is stable from some finite index onward and the theorem monolith supplies the iterate/limit transport, the represented trajectory is eventually constant at the transported limit; the corresponding fixed-point or stationary conclusion then follows when the limiting law is preserved.

Nash existence closes a different obligation: existence of an equilibrium in the specified finite strategic game, using mixed strategies. It does not identify that game's fixed-point correspondence with the GRU/MARL/physics/economic operator automatically. The intended composite theorem therefore needs all of the following links explicitly: Nash/fixed-point existence for the chosen operator; GRU statistical injectivity; exact learner↔Hodge-Maxwell state transport; exact step conjugacy; the eventual stable tail; and the limit-preservation/economic interpretation bridge.

The current `NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem` packages the GRU injectivity, MARL semantics, Hodge-Maxwell representation, four-law witness, and exact iterate transport, but its semantic closure witness `B` is still an explicit premise. The current `StationaryLimitTheorem` likewise requires transition law, convergence, and preservation of the limiting point. Therefore the remaining gap is not GRU injectivity or tail stability; it is the explicit identification of the Nash/economic fixed-point operator with the transported learner/physics operator and the corresponding interpretation witness.
