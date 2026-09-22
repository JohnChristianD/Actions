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
