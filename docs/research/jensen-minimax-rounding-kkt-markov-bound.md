# Horizon-indexed rounding-bias residual regret boundary

Status: connected theorem surface; not an unconditional numeric regret-rate theorem.

The repository's strict optimizer boundary now treats regret as cumulative regret indexed by a finite horizon H. The surviving contracts are:

- Custom optimizer:
  R(H) ≤ J(H) + B(H) + O(H) + M(H).
- F4/Frank-Wolfe:
  R(H) ≤ J(H) + B(H) + W(H) + M(H).

Here R is cumulative regret through horizon H, J is the Jensen/minimax contribution, B is rounding bias, O is a supplied custom-optimizer residual, W is a supplied Frank-Wolfe residual, and M is the stationary/Markov residual. The Agda statements are horizon-indexed pointwise inequalities, rather than scalar regret inequalities.

The important distinction is that this is a residual decomposition, not yet a sublinear regret-rate theorem. A statement such as O(sqrt(H)) or O(log H) would require explicit assumptions and a concrete objective, loss sequence, feasible set, and optimizer dynamics. The current safe monolith does not invent those analytic hypotheses.

## Strict graph boundary

The following standalone surfaces were pruned because they were not required dependencies of the retained consumer theorems:

- ConnectedJensenMinimaxRegretOptimizerTheorem
- ConnectedLionJensenMinimaxRegretRoundingKKTMarkovTheorem
- ConnectedF4FrankWolfeKKTTheorem
- ConnectedF4FrankWolfeJensenRoundingKKTMarkovTheorem

KKT structures may still exist elsewhere in the repository when another theorem actually consumes them. They are not optimizer endpoints here. Likewise, Lion has no strict optimizer endpoint.

The retained consumers are:

- ConnectedCustomOptimizerRoundingBiasRegretTheorem
- ConnectedF4FrankWolfeRoundingBiasRegretTheorem

The F4/Frank-Wolfe consumer depends directly on CanonicalGRUF4NormWatkinsPrefixCompositionTheorem, so the residual is attached to the actual GRU-F4-Watkins composition rather than to a disconnected Frank-Wolfe certificate.

## Maxwell/Tsallis boundary

The Maxwell theorem remains finite-semantics-only:

CanonicalFullLearnerConnectedScanConjugacyTheorem
→ FiniteFunctionExactIsomorphismTransportTheorem
→ ConnectedMaxwellTsallisFiniteExactConjugacyTheorem

The finite theorem requires explicit Maxwell-admissible state semantics, exact finite encoding/decoding, inverse laws, exact transition conjugacy, universal finite exact-function transport, and a finite Tsallis/divergence structure. This is exact representation of the specified finite transition/function; it is not a claim of exact representation of the continuous Maxwell PDE.

The Tsallis carrier remains abstract in Agda. A concrete Tsallis divergence instantiation would need an explicit finite probability/measure representation and its defining laws before promotion. nLab's Maxwell page uses the differential-form equations dF = 0 and d⋆F = j_el; its entropy material treats finite entropy/divergence structure and Tsallis entropy on finite measured spaces. Those sources motivate the semantic boundary, but they do not by themselves prove the repository's concrete finite instance.

## Automation contract

The canonical path remains:

learner_semantic_extractor.m
→ theorem_graph_search.m
→ theorem_monolith_egraph_sync.m

Future theorem admission requires an actual Agda declaration, a real dependency or explicit foundational status, and a consuming composed theorem for optimizer/physics candidates. A scalar regret field is not sufficient for a horizon-regret endpoint; the cumulative regret must be a function of H.

## Verification boundary

This note records the graph/proof-shape contract. It does not claim that the remaining regret theorem has a numerical regret rate, nor that the Maxwell/Tsallis candidate has been promoted to an unconditional physics theorem.
