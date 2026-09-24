# F4 / NormPair / economic injectivity boundary

The F4 boundedness/coercivity question now has an exact negative closure rather than an artificial premise.

The canonical F4 coordinate is `thetaQ : Int8`, with `Int8.code : ℤ`. The step is affine:
`theta' = theta + signal + l2Correction(globalL2)`.
The current kernel does not contain an objective, norm, level-set relation, or real-valued coercivity notion. More importantly, the exact Agda theorem `f4-unit-forcing-linear-growth` constructs the zero-L2/unit-signal trajectory and proves
`code(theta_n) = code(theta_0) + n`.
For any zero-initial theta trajectory, `f4-unit-forcing-no-upper-bound` rules out every constant integer upper bound over all horizons. Therefore unconditional infinite-horizon F4 boundedness is false for the current semantics, and an analytic coercivity theorem cannot be extracted from F4 step-stability alone.

NormPair is not needed for this counterexample. It remains relevant only on the separate representation/economic path:
`F4 stability -> NormPair factor transition -> GRU/F4 economic injectivity -> economic square`.

The economic impossibility is consequently stronger than the previous version. The certificate `F4NormPairEconomicInjectivityCertificate` no longer carries coercivity/boundedness premises. The theorem `noUnconditionalMegaWalrasianExistenceEvenWithF4NormPairEconomicInjectivity` shows that exact F4/NormPair stability, the NormPair factor transition, and economic global-square injectivity still do not imply generalized Walrasian existence.

Graph route:

Economic primitives -> economic update -> exact F4 law -> unit-forcing ray -> no infinite-horizon upper bound.

In parallel:

Economic update -> exact F4/NormPair representation -> NormPair factor transition -> GRU-F4 economic injectivity -> convergence/fixed-point/market-clearing bridge -> generalized Walrasian existence.

The direct edge from information preservation/injectivity to existence is blocked.

Stationarity is a separate issue. The full deterministic learner has a strict clock successor, so `canonicalNoFixedPoint` and `canonicalAperiodic` rule out stationary *states* of the full transition. That does not by itself prove that no probability measure is invariant. A genuine stationary-distribution theorem requires explicit probability/distribution semantics and an invariant-measure proof. The repository already has a conditional `StationaryLimitTheorem` and a `MarkovStationaryWalrasianCompositionTheorem`; they require a supplied convergence/stationary-law witness and a static Walrasian witness.

Thus there is no unconditional general `no Walrasian stationary distribution` theorem here. The defensible impossibility result is narrower and formally strong: the current deterministic learner has no fixed state, F4 has a formally exhibited infinite-horizon growth ray, and even exact F4/NormPair/economic injectivity does not entail Walrasian existence.
