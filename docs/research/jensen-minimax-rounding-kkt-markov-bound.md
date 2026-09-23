# F4 horizon-indexed rounding-bias residual regret boundary

Status: connected theorem surface; no standalone optimizer/KKT endpoint.

The sole custom optimizer is F4. The strict consumer is:

CanonicalGRUF4NormWatkinsPrefixCompositionTheorem
→ ConnectedF4FrankWolfeRoundingBiasRegretTheorem

The certificate carries a per-round regret sequence r(H) and cumulative regret R(H), with the exact horizon law:

- R(0) = 0
- R(H+1) = R(H) + r(H)

For every finite horizon H, the connected theorem establishes:

R(H) ≤ J(H) + B(H) + W(H) + M(H)

where J is the Jensen/minimax contribution, B is rounding bias, W is the F4/Frank-Wolfe residual, and M is the stationary/Markov residual.

This is genuinely time/horizon-dependent. It is deliberately not a claimed asymptotic rate such as O(√H) or O(log H). Such a rate would require explicit loss functions, feasible-set assumptions, optimizer dynamics, and analytic/probabilistic hypotheses.

## Pruned surfaces

Standalone or disconnected optimizer surfaces are no longer part of the canonical theorem source or strict graph:

- Lion optimizer/regret surfaces
- standalone Frank-Wolfe optimizer surfaces
- standalone KKT surfaces
- generic custom-optimizer regret surface
- disconnected Jensen/minimax optimizer surface

KKT is therefore not an optimizer endpoint. A future KKT certificate may enter only if an actual retained composed theorem consumes it.

## QSA boundary

A finite deterministic or exact-algebraic quasi-stochastic-approximation shell can be formalized with discrete exact carriers such as Nat or exact rationals. A convergence theorem for stochastic approximation is different: standard ODE-method proofs use continuous-time limits, stability, probability/noise assumptions, and often measurable, metric, or topological structure. Recent stochastic-approximation work explicitly treats ODE tracking and finite-time tracking error in that analytic setting. citeturn0search0turn0search5

Therefore:
- rationals are not intrinsically required merely to state an exact finite QSA recurrence;
- real analysis is not required for the finite algebraic shell;
- real-analysis, topology, and probability machinery is required once the theorem claims continuous-time limits, almost-sure convergence, asymptotic stability, or stochastic approximation rates.

## Maxwell boundary

nLab presents Maxwell theory in differential-form language as dF = 0 and d⋆F = j on a spacetime manifold. citeturn0search1turn0search4

The repository's finite Maxwell theorem cannot honestly be promoted to exact representation of all continuous Maxwell PDEs. A finite exact-function isomorphism proves exactness only for a specified finite transition/function. Universal Maxwell-PDE representation is a function-space problem.

An actual all-PDE theorem would need:
1. formal differential-form/function-space semantics;
2. a precise domain, metric, source, and boundary/initial-condition model;
3. an exact representation theorem for that function space by the GRU architecture;
4. preservation of dF = 0 and d⋆F = j under representation;
5. an exact encode/decode or function-space isomorphism.

Until those are formalized, the strict boundary remains finite Maxwell exactness rather than universal continuous-PDE exactness.

## Future theorem graph contract

Every future theorem must:
1. exist as an actual Agda declaration;
2. have real dependency edges or be explicitly foundational;
3. expose a consuming connected theorem before becoming a strict endpoint when optimizer/physics-specific;
4. use cumulative horizon-indexed regret for regret claims;
5. keep finite exact representation separate from continuous analytic/PDE representation;
6. pass learner-semantic-extractor → theorem-graph-search → e-graph-sync.

Disconnected theorem declarations are pruned rather than retained as decorative graph nodes.
