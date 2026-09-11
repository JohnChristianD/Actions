# ERL v147 to v158 theorem coverage

This is the canonical migration ledger for the `--safe` learner surface.

| Legacy v147 surface | v158 disposition | Canonical v158 witness |
|---|---|---|
| finite algebraic scalar/order foundation | preserved and strengthened | `OrderedAlgebra` |
| list/vector algebra | preserved | `FeatureVec`, `mapL`, `zipL`, `zipL4`, `sumL` |
| norm pairing | preserved | `NormPair`, `weightL1`, `onePathNorm` |
| two affine stages with SignReLU | preserved | `SignReLULayer`, `twoAffineSignReLULaw` |
| transformer stack composition | preserved | `Stack`, `stackComposition` |
| Tsallis-2 sparse attention boundary | preserved | `Tsallis2State` |
| Munchausen target | preserved with q=2/base-2 naming | `munchausenTsallis2Target`, `munchausenTsallis2CompositionLaw` |
| h-step recursion | preserved | `hStepReturn`, `hStepRecursionLaw` |
| h-step + CEM-Max + True Online composition | preserved | `hStepCEMMaxTrueOnlineLaw` |
| Q-projection idempotence | preserved | `signQProjectionLaw` |
| sign-q-IDBD per-feature direction | preserved | `signQIDBDDirection`, `signDirectionIdempotent` |
| IDBD step-size parameterization | replaced by base-2 exact algebra | `idbdPow2`, `idbdLog2`, `idbdBase2RoundTrip` |
| Lion per-feature moments | preserved | `lionMomentumStep`, `lionPerFeatureDirectionLaw` |
| coupled L2 | preserved in finite dyadic form | `DyadicCoupledL2`, `coupledL2ZeroLaw` |
| VEB-style fitness surface | preserved | `VEBFitness`, `vebFitnessScore` |
| representation-only evolution | preserved | `RepresentationOnlyState`, `representationOnlyLaw` |
| CVT/OpenES emitter state | preserved | `CVTCell`, `OpenESEmitter` |
| antithetic cancellation | preserved | `antitheticFeatureCancel` |
| emergent proximal law | preserved | `proximalSignLaw` |
| emergent Clarke branch law | preserved | `clarkeBranchLaw` |
| emergent median/L1 law | preserved | `medianL1Law` |
| emergent tropical/max law | preserved | `tropicalMaxLaw` |
| whole finite learner state | strengthened | `FullFiniteOrderedRationalLearner` |
| whole finite ordered coupling closure | strengthened | `FullFiniteOrderedRationalCoupling`, `fullFiniteOrderedRationalCoupling` |
| Efficient-CHAD composition boundary | preserved | `EfficientCHADState` plus coupling closure |
| finite local convergence/ranking theorem | **not yet ported into v158** | legacy Stage09 remains separate and is not imported |
| Efficient-CHAD expression/VJP language | **not yet ported into v158** | legacy v147 remains separate |
| replay/barrier/age/staleness surface | **not ported** | intentionally outside current finite learner kernel |
| old LSTM/Gaussian/LayerNorm architecture | **retired** | blocked by CI hygiene policy |
| StoSignSGD/StoSignSGDv2 stochastic sign surface | **retired** | blocked by CI hygiene policy |
| diagonal Newton-Raphson surface | **retired** | blocked by CI hygiene policy |
| certificate-wrapper surface | **retired** | blocked by CI hygiene policy |

## Canonical closure rule

The v158 target is a finite ordered-algebra closure, not a claim that every historical v147 analytic or architectural theorem remains semantically meaningful after the retired architecture is removed. A legacy theorem is carried forward only when it has a type-compatible finite v158 witness; otherwise it is recorded as retired, superseded, or not yet ported.

The CI gate checks the committed v158 source directly with Agda `--safe`; normalization is validation-only and never rewrites source. The scheduled workflow reruns the complete gate hourly.
