# Jensen/minimax regret, rounding bias, KKT, and stationary-Markov boundary

Status: candidate theorem surface, not an unconditional numeric regret theorem.

## Connected theorem

The repository now carries:

`ConnectedJensenMinimaxRegretOptimizerTheorem`

with dependency path:

`CanonicalFullLearnerConnectedScanConjugacyTheorem`
-> `RecurrentAssociativeScanTheorem`
-> `FiniteHardSparseKKTEquilibriumTheorem`
-> `UniqueKKTAbsorbingClass`
-> `MarkovStationaryWalrasianCompositionTheorem`
-> `ConnectedJensenMinimaxRegretOptimizerTheorem`

The quantitative contract is represented as

R <= J + B + K + M

where R is minimax regret, J is the Jensen/minimax gap, B is rounding bias, K is the KKT residual contribution, and M is the stationary-Markov mixing contribution.

The Agda surface proves the arithmetic composition once those component inequalities are supplied. It does not manufacture the component inequalities.

## Why the Jensen step is conditional

Abernethy, Agarwal, Bartlett, and Rakhlin identify optimal regret with a Jensen gap under a minimax-duality formulation of online convex optimization:

https://arxiv.org/abs/0903.5328

The repository therefore treats a concrete Jensen/minimax inequality as an explicit premise rather than importing the result without specifying the loss class, convexity/concavity assumptions, adversarial model, and admissible strategy space.

## Rounding-bias dependency

Low-precision stochastic rounding can introduce a controlled bias. Xia, Massei, Hochstenbach, and Koren analyze stochastic roundoff effects and biased rounding in gradient descent:

https://arxiv.org/abs/2202.12276

Xia, Hochstenbach, and Massei analyze stochastic fixed-point rounding under the Polyak-Lojasiewicz condition:

https://arxiv.org/abs/2301.09511

These results do not automatically instantiate the repository theorem. A concrete rounding map, objective assumptions, and quantitative bias bound remain required.

## KKT dependency

The repository already has `FiniteHardSparseKKTEquilibriumTheorem` and `UniqueKKTAbsorbingClass`. These establish an explicit absorbing-equilibrium interface when their fields are supplied. They do not imply optimizer convergence without an additional stability certificate.

The recent literature also contains direct KKT/stationarity formulations for constrained optimization; one example returned by SciSpace is:

https://doi.org/10.48550/arxiv.2508.18764

## Stationary-Markov dependency

The repository already has `ContinuousStationaryMarkovWalrasianData` and `MarkovStationaryWalrasianCompositionTheorem`. The new theorem composes that existing stationary aggregate interface instead of inventing a stationary law.

For Markovian stochastic approximation, the bias/stationarity relationship has been analyzed by:

https://doi.org/10.1145/3578338.3593526

That result gives a concrete example of why Markov dependence and stationary bias require explicit quantitative assumptions.

## Open proof obligations

1. Instantiate a concrete Jensen/minimax theorem with its convex-concave and duality assumptions.
2. Instantiate a concrete rounding operator and prove its bias bound.
3. Supply the KKT constraint qualification/stationarity certificate for the optimizer.
4. Supply existence/uniqueness and mixing information for the stationary Markov law used by the bound.
5. Prove that all four quantities use the same objective and state representation.
6. Only then promote the candidate from `CANDIDATE_NOT_PROVED` to a proved quantitative regret theorem.

No standalone Jensen, rounding, KKT, or stationary-Markov node is treated as a final theorem in the strict graph. Each is a dependency of the connected optimizer theorem.


## Lion optimization/descent/KKT extension

The connected optimizer boundary now reserves an explicit Lion-specific residual term:

`R <= J + B + K + L + M`

where `L` is a supplied Lion descent/stationarity contribution. This is deliberately a proof input, not an imported convergence theorem.

SciSpace identified three directly relevant results:

- Dong, Li, and Lin, *Convergence Rate Analysis of LION* (2024), arXiv:2411.07724: the paper analyzes Lion as a constrained optimization method and reports convergence to a KKT point at rate `O(sqrt(d) K^(-1/4))` in an `l1`-gradient measure; it also gives an unconstrained critical-point result. https://arxiv.org/abs/2411.07724
- Wang, *Lions and Muons: Optimization via Stochastic Frank-Wolfe* (2025), arXiv:2506.04192: Lion and Muon with weight decay are interpreted as stochastic Frank-Wolfe instances; convergence is measured by the Frank-Wolfe gap, and under a norm constraint this gap implies convergence to a KKT point. https://arxiv.org/abs/2506.04192
- Jiang and Zhang, *Convergence Analysis of the Lion Optimizer in Centralized and Distributed Settings* (2025), arXiv:2508.12327: reports `O(d^(1/2) T^(-1/4))` for standard Lion under stated assumptions and `O(d^(1/2) T^(-1/3))` for a variance-reduced variant, with distributed/communication-efficient variants. https://arxiv.org/abs/2508.12327

These results strengthen the research basis for the optimizer seam, but they do not automatically prove the repository's connected theorem. In particular, the repository still needs one shared objective/state representation, an explicit Lion update rule, the exact smoothness/noise assumptions used by the selected convergence result, a descent or stationarity inequality that yields `L`, and a KKT constraint-qualification/multiplier witness compatible with the existing KKT record.

The graph therefore contains `ConnectedLionJensenMinimaxRegretRoundingKKTMarkovTheorem` and `CanonicalLionSignMomentumKKTDescentBoundaryCandidate` as `CANDIDATE_NOT_PROVED`. They are not standalone separation theorems. The Lion seam is consumed by the connected Jensen/minimax/rounding/KKT/Markov optimizer boundary, preserving the no-disconnected-theorem rule.

### Updated open obligations

1. Instantiate the Jensen/minimax duality witness.
2. Instantiate the rounding map and quantitative bias bound.
3. Instantiate the KKT constraint qualification and stationarity/multiplier witness.
4. Instantiate the Lion update and descent/stationarity certificate producing `L`.
5. Prove compatibility between the Lion stationarity measure and the repository KKT residual.
6. Supply stationary Markov fixed-point existence/uniqueness and quantitative mixing/error information.
7. Prove all terms use the same objective, state, horizon, and rounding representation.
8. Only then promote the connected candidate to a proved quantitative regret theorem.


## F4 + Frank-Wolfe correction

The optimizer-specific seam is F4 + Frank-Wolfe, not a request for another Lion theorem.

The repository already has an exact finite F4 recurrent component through C.F4IntUState, C.f4ThetaStep, and CanonicalGRUF4NormWatkinsPrefixCompositionTheorem. The new connected boundary is ConnectedF4FrankWolfeKKTTheorem. It carries only a finite certificate:

FWgap <= D_F4 + K

where the Frank-Wolfe gap, an F4 descent residual, and a KKT residual are explicit finite proof inputs. No optimization library was added.

SciSpace confirms the relevant mathematical seam. Wang, Lions and Muons: Optimization via Stochastic Frank-Wolfe (2025), DOI 10.48550/arXiv.2506.04192, explicitly connects convergence in the Frank-Wolfe gap with KKT convergence under a norm constraint. Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization (2013), provides the duality-gap certificate framework. Oliveira, A note on the Frank-Wolfe algorithm for a class of nonconvex and nonsmooth optimization problems (2023), DOI 10.5802/ojmo.21, gives stationarity results for a nonconvex/nonsmooth class. These are research inputs, not automatically Agda facts.

The eventual optimizer-regret composition may therefore have the form

R <= J + B + K + L + W + M

with W the Frank-Wolfe contribution, but this is still a candidate composition until the F4 state, objective, feasible set, FW update, gap-to-KKT theorem, Jensen witness, rounding bias, Lion term if retained, and stationary-Markov term are represented over one shared state/objective.

## Maxwell-only finite representation boundary

No additional physics library or theorem library was introduced. The graph now contains a candidate FiniteMaxwellGRUExactRepresentationCandidate.

Its scope is intentionally narrower than “a GRU represents all physics”: it asks whether a finite exact representation can encode a specified finite Maxwell-admissible transition system. The graph must not silently introduce gravity, quantum dynamics, thermodynamics, or other physical laws. Exact finite-function representability does not by itself prove the continuous Maxwell PDEs; a finite state semantics, discretization/update rule, and exact encoding/conjugacy are required.

The existing FiniteFunctionExactIsomorphismTransportTheorem is the representation mechanism. Mercury A*/e-graph can search and compose these finite theorem interfaces, while the graph's promotion gate prevents an unsupported Maxwell claim from becoming a proved theorem.

### Current open obligations

1. Give the exact finite F4 state/update semantics used by the Frank-Wolfe objective.
2. Give the Frank-Wolfe feasible set and linear minimization oracle.
3. Prove the FW-gap/descent-to-KKT implication required by the chosen assumptions.
4. Connect that certificate to the existing F4 recurrent prefix theorem.
5. If composing into regret, share one objective/state with Jensen, rounding, KKT, Markov, and any retained Lion seam.
6. Define the finite Maxwell state/input/output encoding.
7. State the discrete Maxwell constraints/update being represented.
8. Prove exact GRU encoding/decoding or conjugacy for that finite Maxwell transition.
9. Keep Maxwell as the physical-law boundary; do not promote unsupported additional physics.
10. Run the Agda/Mercury/e-graph verification before promoting either candidate.
