# Meta-Search Architecture

The canonical learner keeps its model parameters, imports, and formal semantics manual. Automated search is allowed to vary only a closed seven-slot A/Q program genome.

## Roles

| Layer | Role |
|---|---|
| Agda | Executable learner semantics, finite benchmark environments, theorem checking, and final certificate gate |
| Mercury | Typed finite candidate grammar plus proof-friendly EvoSAX-family meta-search |
| JAxtar A/Q boundary | Typed graph-search vocabulary for A*/Q*-style candidate traversal |
| Guix/Guile | Reproducible orchestration and tool pinning |
| Manual source | Learner parameters, imports, carrier choices, and theorem assumptions remain explicit |

The present Mercury meta-search includes finite analogues of Random Search, Hill Climbing, Simple ES, OpenES, PGPE, SNES, and CMA-ES. These are deliberate exact/discrete search kernels over the finite A/Q genome, not a JAX or Python port of EvoSAX floating-point numerics.

## Lion-style process

The intended discovery loop is:

1. Start from a typed program grammar.
2. Generate and mutate candidate programs with a strategy portfolio.
3. Score candidates on exact symbolic constraints and, where wired in, Agda closed-loop benchmark results.
4. Select and simplify candidates.
5. Pass only surviving candidates to the Agda theorem/benchmark gate.
6. Record the accepted candidate as a reproducible certificate.

This follows the important structural idea from symbolic algorithm discovery: search over programs first, then use selection and simplification to turn discovered programs into compact algorithms. It does not claim to reproduce Google's original Lion search implementation.

## JAxtar relationship

JAxtar is treated as the natural A*/Q* graph-search reference for the outer candidate-navigation problem. The repository does not import the JAX engine. The existing Mercury/Agda JAxtar surface is a finite typed A/Q graph and certificate boundary.

The useful combination is therefore:

    JAxtar-style A*/Q* graph traversal
        +
    EvoSAX-style proposal/update kernels
        +
    Agda exact execution and theorem checking

MCTS is not required merely to obtain this search topology. MCTX can remain an external alternative when an explicit MCTS branch is desired.

## TSTS + PVS outer search boundary

The outer search now distinguishes branch selection from exact verification:

    TSTS posterior sample / tree choice
        ->
    PVS principal-branch recheck
        ->
    canonical Agda evaluator
        ->
    endogenous learner observables

TSTS is the only candidate in this comparison that arrives with the specific finite-time Bayesian regret guarantee used to justify the tree-selection layer. PVS is a correctness-preserving alpha-beta search organization, not a regret guarantee. The repository therefore treats TSTS as the search-selection theory and PVS as the exact recheck mechanism.

The Mercury discovery grammar includes TSTS+PVS with GESMR, SAMR, SimpleES, and RandomSearch challengers, plus PVS-only, PVS+HillClimbing, and MCTX+PVS alternatives. The selected candidate is accepted only when it also satisfies the existing endogenous F4/L2 -> Watkins -> GRU/F4 tell and preservation obligations.

## SIMD-friendly library boundary

The target is not wholesale JAX or TensorFlow replication. The library boundary should instead favor compact array-friendly primitives that can map naturally onto SIMD-oriented implementations, while leaving the learner's formal parameterization and theorem source explicit.

That keeps the runtime substrate small without allowing an external numerical library to become the source of truth.

## Why GESMR emerged for the endogenous composition

The search grammar now includes MR15_GA, GESMR_GA, Open_ES, HillClimbing, PSO, DifferentialEvolution, and an MCTX search candidate.

The requirement set is intentionally semantic rather than name-based:

- elitist population selection;
- adaptive mutation rate;
- grouped mutation rates;
- canonical Agda learner evaluation;
- Watkins/F4-L2/GRU tell coupling;
- NormPair preservation;
- persistent-GRU preservation.

Under that grammar, MR15_GA satisfies the adaptive-mutation and elitist-population properties but does not supply grouped mutation rates. MCTX supplies tree-search behavior, not mutation-rate adaptation, so it is a candidate-navigation mechanism rather than the selected evolutionary update rule. HillClimbing supplies local search but not the grouped-rate population semantics.

GESMR_GA is therefore the first candidate accepted by this exact finite semantic gate.

The distinction is important: the Mercury lane discovers a candidate from a typed property grammar. The Agda theorem then supplies the exact symbolic semantics for the candidate's composition with the existing learner. It does not claim that the external JAX implementation has been numerically reproduced.
