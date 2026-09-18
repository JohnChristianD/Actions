# Meta-Search Architecture

The canonical learner keeps its model parameters, imports, and formal semantics manual. The active automated search layer is deliberately narrower: it uses a TSTS-style tree over a finite grammar of endogenous learner-composition branches. There is no active evolutionary-algorithm population search and no active JAxtar/A*/Q* graph-search adapter.

## Roles

| Layer | Role |
|---|---|
| Agda | Executable learner semantics, finite benchmark environments, theorem checking, and final certificate gate |
| Mercury | Typed finite TSTS composition boundary and reproducible discovery report |
| Guix/Guile | Reproducible orchestration and tool pinning |
| Manual source | Learner parameters, imports, carrier choices, and theorem assumptions remain explicit |

## TSTS-only process

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

## Why PVS and JAxtar were removed

PVS is an alpha-beta search optimization for minimax trees, not a second correctness oracle for this learner. Keeping it beside TSTS would add a search-policy layer whose objective is unrelated to the exact endogenous learner score.

JAxtar is an A*/Q* graph-search implementation. It is useful for graph-navigation problems, but the present grammar is a small tree of alternative learner-composition branches, so a second graph-search adapter would duplicate the outer navigation role.

Evolutionary proposal families such as OpenES, MR15-GA, SAMR-GA, and GESMR-GA are also retired from the active composition search. Their mutation/population state is orthogonal to the theorem we are trying to discover and would reintroduce a second optimization state.

## TSTS endogenous loop

The active search boundary is:

    posterior sample
        ->
    branch selection
        ->
    exact learner probe
        ->
    canonical Watkins target
        ->
    reward / posterior witness update
        ->
    next TSTS selection

The important change is that the search reward is endogenous. It is not a detached fitness function. For the selected branch, the reward is obtained from the learner's own canonical Watkins target, which already contains attention, GRU, F4/L2, and q-log feedback. The same target then drives the GRU and F4 tells.

This creates a single closed causal loop without requiring PVS, JAxtar, or an evolutionary population.

## Literature boundary and novelty discipline

The constituent techniques are not new individually. Greshler et al. introduce TSTS and prove a finite-time Bayesian regret bound in their online-planning setting. REx uses Thompson Sampling to choose which program to refine, and recent work has also used Thompson-sampling tree search over program/code hypotheses. These establish clear adjacent prior art.

The repository's narrower claim is therefore not “new Thompson sampling,” “new program search,” or “new exact verification.” The novelty candidate is the exact finite connected composition in which:

1. TSTS selects among endogenous learner perturbations.
2. The selected perturbation is evaluated by the same executable Agda learner.
3. The reward is the learner's endogenous Watkins target.
4. That target is simultaneously consumed by the GRU and F4 tell paths.
5. The reward is written back into the TSTS posterior witness.
6. NormPair and persistent-GRU invariants survive the closed step.

A literature search found adjacent Thompson-sampling program-search and code-refinement systems, but I did not find this exact formal composition in the sources checked. That supports a narrow “apparently not previously reported” claim, not a definitive priority or mathematical-literature novelty claim.

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
