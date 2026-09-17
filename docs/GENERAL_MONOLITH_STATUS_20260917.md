# General full-coupled monolith status

Date: 2026-09-17
Branch: `main`

## Learner surface

`Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda` is the generalized learner surface. Its policy head is indexed by arbitrary `A`:

```text
QVec A = Fin A -> Int8
CountVec A = Fin A -> Nat
sparsemaxPolicy : ActionSpace A -> QVec A -> CountVec A -> Fin A
```

`actionSpace2`, `actionSpace4`, and the 64-action default are concrete fixtures, not a restriction on the policy type. The old `CanonicalLearnerMonolith.agda` remains a legacy two-action architecture and should not be read as the definition of the generalized policy.

The generalized monolith now uses the standard-library finite list sorting/order surface (`Data.List.Sort`, `DecTotalOrder`, lexicographic product order) rather than its former handwritten list/sort carrier. `FiniteRational` is still handwritten in the learner monolith; it is not a standard-library rational type.

## Theorem monolith

`Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda` depends only on the generalized learner monolith. It now contains:

```text
gruPersistentLaw
gruStep-respects-equivalence
MobiusTrace / prefixAction / traceInput
traceGRU
traceGRU-unbounded
semidirect-product-law
trace-prefix-semidirect-composition
trace-depth-invariant
```

`traceGRU-unbounded` identifies the recursively iterated GRU transition with the depth-indexed semidirect Mobius scan, so a different `MobiusAction` can occur at every depth.

The theorem surface also contains a finite piecewise-rational syntax and closure under hard-sign branching, input-map composition, and arbitrary finite natural depth. The stronger `Exotic/ERL/FullCoupled/FinitePiecewiseRationalClosure.agda` module adds a well-formedness invariant: every denominator produced by the finite surface is provably nonzero, including every finite-depth iterate. This is a closure theorem for a finite piecewise-rational representation surface, not a universal-approximation theorem.

## GRU activation boundary

The generalized `gruStep` implementation itself consumes `hardSignGate` and finite `Int8` arithmetic. The learner separately defines `FiniteRational` and `mobiusRatio`, and the theorem surface uses `mobiusRatio` to build the piecewise-rational representation, but `gruStep` does not directly consume `mobiusRatio` or a `FiniteRational` activation. Therefore the implementation should not be described as a literally Möbius-activated rational GRU without an explicit bridge definition.

## Reservoir-computing boundary

The current Agda surface does not establish the reservoir-universality or attractor-storage theorems from the associative neuronal-assembly literature. To apply those results to the GRU, the formalization would still need a reservoir dynamical-system contract, a readout/training model, and the paper-specific assumptions such as the relevant recurrence/coupling structure, memory or synchronization condition, and an attractor-storage/retrieval theorem. The 2025 necessary-and-sufficient reservoir result is especially useful as a checklist because it characterizes universality through explicit reservoir conditions rather than equating finite-depth recurrence with universality.

The current finite `GRUState` carrier and the natural-number depth index therefore give an unbounded family of finite-depth computations, but they do not by themselves establish universal approximation of arbitrary dynamical systems or storage of an arbitrary family of attractors.

## KKT status

The arbitrary-A sparsemax KKT theorem is **not complete**.

The theorem monolith currently contains finite KKT boundary records and conditional certificate types. It does not prove that the concrete `L.sparsemaxWeight` / `L.sparsemaxPolicy` scan constructs a valid primal-simplex, stationarity, and complementarity certificate for every finite `A`, nor that this finite Int8 construction is equivalent to the usual real-valued Euclidean sparsemax projection.

That boundary is intentional. No theorem name is being used as a shell around an unproved construction.

## CNN theorem status

The theorem monolith now contains a stronger theorem-only CNN class:

```text
StandardCNNStack
standardCNN-depth-equivariant
CNNLearnerComparison
cnnLearner-trajectory-bisimulation
```

The comparison is purely semantic. No concrete CNN implementation is imported into learner semantics. A commuting representation witness yields finite-depth trajectory bisimulation by induction.

This is stronger than the previous reflexive depth factorization, while still not a claim of equality with every conventional CNN architecture.

## Benchmark surface

Active additional ports:

```text
POBAX T-Maze
Gymnax GaussianBandit-misc slot with Uniform reward semantics
Jumanji/pgx 2048 projection
```

RockSample has been removed from `CanonicalClosedLoopBenchV2.agda`. Maze-v0 remains excluded from the current closed-loop result sheet.

Exact deterministic replay results from `GENERAL_CLOSED_LOOP_BENCH_RESULTS_20260917.md` include:

```text
Pong, horizon 16:
  no-Munchausen             return 16  regret -8  success 0  steps 16  distinct 3
  negative-Q-Munchausen     return 16  regret -8  success 0  steps 16  distinct 3

POBAX T-Maze, horizon 8:
  no-Munchausen             return 0   regret 1   success 1  steps 2   distinct 1
  negative-Q-Munchausen     return 0   regret 1   success 1  steps 2   distinct 1

Uniform GaussianBandit slot, horizon 16:
  no-Munchausen             return 1   regret 15  success 0  steps 16  distinct 2
  negative-Q-Munchausen     return 8   regret 8   success 0  steps 16  distinct 2

Jumanji/pgx 2048 projection, horizon 32:
  no-Munchausen             return 222 regret -190 success 0 steps 32 distinct 4
  negative-Q-Munchausen     return 269 regret -237 success 0 steps 32 distinct 4
```

The negative-Q-Munchausen arm remains the repository's canonical finite sign-flipped scale. These deterministic replays are not a statistical study and do not establish CNN replacement capability.

## Import recommendation

`Data.List.Sort.MergeSort.Properties` is algorithm-specific and explicitly recommends using `Data.List.Sort` unless a particular MergeSort property is needed. `Relation.Binary.Properties.DecTotalOrder` supplies generic order properties once a `DecTotalOrder` is already present. Neither library proves sparsemax KKT by itself.

Therefore the current minimal path is:

```text
keep the generalized learner's standard-library Data.List.Sort surface
add Relation.Binary.Properties.DecTotalOrder only if order-structure proofs
actually replace handwritten order lemmas
add Data.Rational only if the KKT proof is intentionally promoted from
finite Nat/Int8 certificates into exact rational semantics
```

Adding both sorting-property stacks solely for KKT would enlarge the import graph without closing the KKT construction gap.

## Maintenance boundary

This page should be reviewed whenever the generalized learner changes its carrier types, the theorem monolith changes its finite-piecewise-rational grammar, or the reservoir formalization gains actual universality/attractor hypotheses. The benchmark-results block is historical evidence and must be replaced only when the corresponding benchmark semantics and result ledger are regenerated.
