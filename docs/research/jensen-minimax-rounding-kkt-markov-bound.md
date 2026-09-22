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
