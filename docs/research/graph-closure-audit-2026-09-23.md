# Graph closure audit — 2026-09-23

## Verified scope

This audit resumes the connected-theorem graph from the 2026-09-22 closure work. The proof authority remains Agda `--safe`; Mercury discovery/e-graph output is graph infrastructure, not proof.

## Maxwell exact-representation boundary

nLab gives the classical Maxwell system in differential-form form as

`d F = 0`

and

`d ⋆F = j_el`

with (F) a differential 2-form, (j_{el}) a current 3-form, (d) the de Rham differential, and (⋆) the Hodge star. The same page expands these into magnetic Gauss, Faraday, electric Gauss, and Ampère-Maxwell laws. The nLab Hodge-Maxwell theorem gives the corresponding closed/coexact representative statement on compact oriented Riemannian manifolds.

That does not by itself supply a finite GRU representation. The repository's existing `FiniteMaxwellGRUExactRepresentationCandidate` is correctly still a candidate: an exact finite representation needs an explicitly chosen finite state space, discrete Maxwell constraints/update, exact encoder/decoder, and a proved transition conjugacy. Without those data, claiming exact representation of the continuous PDEs would invent a discretization.

Therefore the completed conclusion is:

- all four classical Maxwell PDE laws are already unified by the differential-form pair `dF = 0`, `d⋆F = j`;
- the Hodge-Maxwell existence/uniqueness statement is a separate analytic theorem, not a finite-state transition theorem;
- the repository can honestly promote only a specified finite Maxwell discretization after its semantics and exact conjugacy are supplied;
- no continuous-PDE-to-finite-GRU theorem should be fabricated from the current finite UAP surface.

## F4 / rounding-bias / residual regret

The current connected Agda surface contains the conditional F4/Frank-Wolfe/Jensen/rounding/KKT/Markov composition

`R ≤ J + B + K + W + M`

and the broader Lion extension

`R ≤ J + B + K + L + W + M`.

These are additive certificate compositions. They do not contain a horizon parameter or a theorem saying that the bound is monotone in horizon.

Hence the precise answer is: horizon monotonicity is not currently proved for the repository's optimizer boundary. It becomes provable under an additional horizonized definition, for example nonnegative cumulative regret (R_H = Σ_{t < H} r_t) with (r_t ≥ 0), or under componentwise monotonicity of the horizon-indexed certificate terms. The existing theorem cannot be silently upgraded because its data record has no such horizon law.

## Tcl

A repository-wide search found Tcl only as a direct `pkgs.tcl` entry in `flake.nix`; no CI script, Dhall lane, Mercury source, Agda source, or workflow invokes Tcl by name. The direct dev-shell dependency was therefore redundant for the current repository.

The direct `pkgs.tcl` dependency has been removed from `flake.nix`. This is a present-use conclusion, not a claim about every possible future contributor script: if a future theorem/discovery tool actually requires Tcl, it should add the dependency at that point.

## Disconnected-theorem pruning and promotion

The graph keeps the no-synthetic-edge rule. A theorem with no real consumer remains foundational rather than being promoted merely to make the graph connected.

The promotion order remains:

`foundational theorem -> smallest existing composed consumer -> full connected learner -> F_full_connected`.

Existing connected consumers already absorb many previously isolated records, including recurrent scan/conjugacy, endogenous observation/topology, Haar/sparsemax closure, and the F4/Frank-Wolfe optimizer seam.

## Future theorem graphing

The current Mercury graph search already has named plans for the connected optimizer boundaries and `FiniteMaxwellGRUExactRepresentationCandidate`, and its generic composite-law search walks actual extracted dependencies. Future theorem admission therefore remains:

1. actual Agda proposition;
2. actual dependency into an existing composed consumer;
3. discoverability by `theorem_graph_search`;
4. e-graph synchronization;
5. candidate status until witnesses exist;
6. strict separation only after inclusion, connected witness membership, and baseline nonrepresentability.

No conceptual similarity is an edge.

## Novel exotic candidates still open

The graph still contains candidate-only routes, including:

- `FiniteMaxwellGRUExactRepresentationCandidate`;
- `CanonicalEndogenousFiniteVocabularyRecurrentSequenceClosureCandidate`;
- HardSign/finite-automaton factor-geometry routes;
- non-tropical sign/optimizer-affine routes;
- learner-replacement quotient routes;
- `ConnectedLionJensenMinimaxRegretRoundingKKTMarkovTheorem`;
- the F4/Frank-Wolfe/Jensen/rounding/KKT/Markov boundary where the required shared-state analytic witnesses are not all present.

The existing literature-aligned exact-clock versus finite-state separation is already a proved Agda composition; the route-specific exotic mechanisms are not automatically proved by that shared witness.

## Recent transformations

The 2026-09-22 history contains genuine mathematical transformations, not just repairs:

- `dcfdde047e276a1a22d9634f1a75354080d6cd41`: added the nonlinear sequence-storage/generation algebraic proof;
- `d53313518cf4cce673f1ac108fec075e007f6e6d`: added the internal verification boundary and HardSign/automaton candidate surface;
- `f8a3826d7e...`: promoted pre-graphed automata/HardSign seams into the connected graph;
- the learner-replacement quotient commits added another distinct candidate route.

The later recurrent-lookup and Mercury-import commits were repairs, not mathematical transformations.

## Final status

The graph is not made "complete" by turning every candidate into a theorem. It is complete when every real dependency is discoverable and every unsupported edge remains visibly candidate-only.

The two material open mathematical obligations that cannot be honestly closed from the current repository are:

1. exact finite Maxwell semantics + exact GRU conjugacy for a specified discretization;
2. horizon-indexed optimizer regret monotonicity with explicit nonnegativity/shared-state assumptions.

Everything else above is a classification/graph-closure decision rather than an invented proof.
