# General closed-loop learner bench

## Monolith boundary

`Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda` is the single self-contained learner component. It contains the finite action abstraction, Int8 finite arithmetic, score ordering, threshold-style sparsemax weights, Q/count state, Mobius trace, GRU state and transition, F4-style quantizer, norm state, and canonical finite negative-Q-Munchausen mode. It contains no theorem layer.

The theorem layer is `GeneralFullCoupledTheoremsMonolith.agda`, whose only learner dependency is the learner monolith.

## Sparsemax status

The old hard-coded 2-action boundary is removed. The learner accepts arbitrary finite `ActionSpace A`, with checked inhabitants for `A = 2`, `4`, and default width `64`.

The learner exposes the exact finite threshold numerator/denominator representation and a largest-valid-support scan. The theorem monolith now contains arbitrary-`A` KKT certificate types and the direct simplex/denominator consequences of a supplied certificate. It does **not** yet prove that the learner's Int8 scan constructs a certificate for every bounded `A`; that algorithm-to-KKT bridge remains the genuine gap.

No extra algebraic library is required merely to state this bounded finite-A KKT layer. The current learner's nine standard-library imports already provide Nat arithmetic, finite indices, finite modulo construction, products, and propositional equality. An order-property bundle can shorten sorting proofs, but it is not mathematically required by the KKT structure itself.

## Counterfactual rational versus order imports

`Relation.Binary.Properties.DecTotalOrder` supplies generic decidable-total-order consequences such as flipped-order laws and total-order structures. It is the more minimal counterfactual import when the existing finite implementation remains Nat/Fin-based and the proof need is ordering, threshold maxima, and sorted support scans. It does not provide a rational number carrier or division.

`Data.Rational.Base` supplies canonical reduced rationals with integer numerators, positive natural denominators, and coprimality invariants. It is useful only when the formal target itself is an exact rational number layer. It introduces substantially more arithmetic structure than the current learner needs, and it would not by itself establish sparsemax KKT.

No rational import is added here.

## Mobius/GRU semidirect coupling

`MobiusTrace = Nat -> MobiusAction` gives a depth-indexed action rather than a single fixed Mobius map. The theorem monolith proves prefix-action recursion, semidirect one-step factorization, direct coupling to the iterated GRU transition, arbitrary finite-depth trace iteration, and the depth-invariant persistent token tuple `(matrixZ, matrixR, matrixH, optimizerToken)`.

## External CNN theorem boundary

The theorem monolith uses an abstract finite-depth machine with an encoder, local step, translation action, equivariance law, representation adapter, downstream transition, and a theorem-only `StandardCNNStack`. The proof establishes finite-depth equivariance and lifts a one-step commuting witness into trajectory bisimulation.

No concrete convolution kernel, tensor layout, padding rule, stride, learned parameter tensor, or trained CNN is embedded into learner semantics.

## Closed-loop bench

`GeneralClosedLoopBenchV2.agda` executes:

`learner state -> policy -> finite action -> environment step -> reward/next state -> learner step`.

The active suite has exactly these 12 environments:

`CartPole-quantized`, `BernoulliBandit`, `MetaMaze`, `FourRooms`, `Jumanji Knapsack`, `LevelBasedForaging`, `Pong`, `MemoryChain`, `DiscountingChain`, `POBAX T-Maze`, deterministic `Uniform` replacement in the Gymnax GaussianBandit-misc slot, and a finite `Jumanji/pgx 2048` projection.

RockSample and Maze-v0 are excluded.

The published results sheet reports only return, regret/shortfall, executed steps, and distinct actions. Terminal success is not reported because it is derivable from the environment termination convention and does not add a separate learner-performance axis for this suite.

## Verification

`.github/workflows/agda.yml` contains the Agda `--safe` CI gate and explicitly checks the generalized learner monolith, theorem monolith, generalized closed-loop benchmark, and additional benchmark ports. The workflow uses Agda `2.8.0` with stdlib `2.4`.

The current connector session has not exposed a completed workflow run for the latest direct commits, so compiler verification should be read from the CI run itself rather than inferred from the commit alone.
