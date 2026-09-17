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

The generalized monolith currently has six direct standard-library imports. It still uses its own finite list/sort and finite arithmetic definitions. Adding a sorting or rational library is therefore a deliberate proof-scope decision, not a requirement of the learner surface.

## Theorem monolith

`GeneralFullCoupledTheoremsMonolith.agda` depends only on the generalized learner monolith. It now contains:

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
keep the learner's existing finite sort
add Relation.Binary.Properties.DecTotalOrder only if order-structure proofs
actually replace handwritten order lemmas
add Data.Rational only if the KKT proof is intentionally promoted from
finite Nat/Int8 certificates into exact rational semantics
```

Adding both sorting-property stacks solely for KKT would enlarge the import graph without closing the KKT construction gap.
