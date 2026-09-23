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


## 2026-09-23 continuation: exact finite discretization

The previous boundary has now been separated into two explicit Agda layers.

ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem remains a theorem about a declared finite family of continuous differential-form solutions. Its finite carrier is an exact encoding of that family, not a numerical approximation of the full continuous solution space.

FiniteHodgeMaxwellExactDiscretizationTheorem is now a separate theorem. Its certificate supplies finite discrete 2-form, Hodge-star, and 3-form carriers together with discrete operators and exact commuting laws for d, star, d-star, zero, and current. The discrete 3-form encoding is required to be injective, which gives both directions:

- continuous Maxwell equations imply the discrete equations exactly;
- discrete equations imply the declared continuous Maxwell equations exactly.

The fully connected consumer ConnectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem combines those two layers only after an explicit shared-semantics equality is supplied. This closes the finite-discretization ambiguity without asserting a finite representation of the full infinite-dimensional PDE solution space.

The repaired Maxwell semantics now model the Hodge star through a separate FormStar carrier and an explicit dStar : FormStar -> Form3. This avoids identifying the Hodge star with an endomorphism of 2-forms, which is not dimension-general: nLab describes the Hodge star on p-forms as landing in (n-p)-forms, and in four-dimensional Maxwell theory the Faraday 2-form is sent to another 2-form only because 4-p = 2. citeturn767860search3turn767860search8

The source basis remains the nLab differential-form Maxwell equations dF = 0, d⋆F = j and the Hodge-Maxwell theorem's exact representative statement on compact oriented Riemannian manifolds. citeturn767860search0turn767860search2

## Tcl versus Dhall

The current repository needs no direct Tcl dependency. The pinned Nix shell now contains Mercury and Dhall only, while Dhall is used as a total configuration language to generate shell text that is then executed by the normal shell environment.

Dhall is indeed total and normalizing rather than Turing-complete, with evaluation guaranteed to terminate for type-correct expressions. Its official documentation also describes it as a programmable configuration language and documents integrations that read Dhall or render it into external formats. Those properties do not make Tcl globally redundant: Dhall does not itself replace an arbitrary Tcl runtime or every process-oriented scripting environment. The correct future rule is dependency-on-demand: keep Tcl absent now, and add it only when a future repository tool has a demonstrated Tcl runtime dependency. citeturn893290search0turn893290search1turn893290search2

## Post-closure recent commit classification

The commits after the prior closure contain one substantive mathematical promotion and several graph repairs/synchronizations.

7dea0190f1aeb0cf56022633b6b9ce5cd778757a is transformative: it promotes the exact finite continuous Hodge-Maxwell representation and relaxes the QSA promotion boundary only where the existing composed analytic interfaces justify it.

d93fe8c8afa791bc33d2bf939cb6b59db285c376 is graph infrastructure: dependency-search registration.

5603d69db122b4ada1375de9819142b56a204ab5 is graph infrastructure: e-graph gate alignment.

868186d0d856b640aa40653bd545067ce0e7e167 and 468c4cecf54c0693c19db6437b41d99fcf61b314 are pruning repairs: the stale Maxwell candidate was removed after promotion. They do not introduce a new mathematical theorem.

## Remaining candidates

The newly pre-graphed frontier is FiniteDiscreteHodgeMaxwellStarInvolutionCandidate. It is deliberately candidate-only because a same-degree involution is not a general property of the Hodge star across arbitrary dimensions/signatures, and the exact discretization theorem does not need it.

The full continuous-PDE representation candidate remains unpromoted. Exact finite encodings plus exact finite discretization are not sufficient to prove an exact finite-state representation of the full infinite-dimensional Maxwell solution space.


## Updated closure status

The finite-discretization obligation is now closed conditionally and explicitly: the Agda surface contains preservation and reflection for a supplied finite Hodge-Maxwell discretization certificate, plus a composed consumer that also consumes the continuous finite-family GRU theorem's Maxwell field-equation witness.

The F4 surface also already contains conditional horizon monotonicity from nonnegative per-round regret. The remaining optimizer boundary is therefore not missing a basic monotonicity lemma; the stronger quantitative rate remains certificate-dependent.

The remaining Maxwell frontier is the full continuous PDE/function-space representation claim. That remains candidate-only because neither finite encoding nor finite discretization yields a theorem about the whole infinite-dimensional solution space. The optional same-degree finite Hodge-star involution is likewise candidate-only.
