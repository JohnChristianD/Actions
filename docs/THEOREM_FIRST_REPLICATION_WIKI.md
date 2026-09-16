# Theorem-first canonical learner replication prompt

This document is the replication authority. Agda `--safe` proof terms are authoritative. Game environments remain external modular test fixtures. Haskell scripts are audits only.

## 1. Canonical learner boundary

Canonical source:

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

The canonical learner is environment-agnostic and has no project-local Agda imports.

Direct standard-library imports:

```text
Relation.Binary.PropositionalEquality
Agda.Builtin.Nat
Data.Nat
Data.Fin
Data.Fin.Properties
Data.Nat.DivMod
Data.Product
Data.Empty
```

No additional standard-library module is currently required by the canonical learner source. Extra algebraic libraries are not needed merely because the mathematics has names such as semiring, norm, Möbius map, or sparsemax. The maintained proofs use finite data, Nat arithmetic, equality/negation, products/records, and endomorphism composition.

## 2. Default width

Replication default:

```text
d = 64 = 4^3
```

The width witness is separate from the current scalar `GRUState`. The current GRU carrier has one Int8 hidden coordinate. A genuine d-dimensional GRU requires a d-vector carrier and d-dimensional transition functions.

The current Int8 H4 result is the exact unnormalized relation

```text
H4 * H4^T = 4 I  (mod 256)
```

This is orthogonality. It is not normalized orthonormality in `Z/256Z`, since 2 has no inverse modulo 256.

## 3. Algebraic minimum

The maintained learner is below ring theory in its actual proof requirements:

```text
finite many-sorted data
+ Nat arithmetic
+ equality and negation
+ products and records
+ End(S) under composition
```

`End(S) = S -> S` is the composition monoid used by the GRU/Möbius scan theorems. Ring laws are not required by the learner proofs.

`FiniteRational` is a finite encoding record. It is not a proved rational field, so the current source does not claim unrestricted analytic division or real-valued rational-function completeness.

## 4. Sparsemax action width

The canonical policy head is exactly

```text
Sparsemax2Pair = Int8 × Int8
```

and `policyChoosesLeft` decides between two actions.

Therefore the current canonical policy is genuinely two-action. Larger environment action spaces use explicit adapters in `CanonicalClosedLoopBenchV2.agda`; those adapters are finite test interfaces and are not a theorem that the existing sparsemax head is general-A.

A true general-A sparsemax theorem would require an explicit A-indexed score vector, the sparsemax threshold/support construction, and a proof that the resulting weights satisfy the desired finite normalization/support laws. That theorem is not claimed yet.

## 5. Closed-loop learner interface

The old reward-injection regression was not a genuine RL loop because its critic path ignored the injected reward. That wiring defect is now isolated and replaced by `CanonicalClosedLoopInterface.agda`.

The maintained interface is:

```text
learner state
  -> learner chooses action
  -> external game step(action,state)
  -> observation, next state, reward, done
  -> action-conditioned learner update
  -> next learner state
```

The interface records:

```text
return
reference return
regret = reference return ∸ return
success
steps
```

The learner clock theorem proves one unit of learner progress per executed update.

This is an executable deterministic finite interface. It is not a claim that the current quantized game projections reproduce upstream floating-point or stochastic execution bit-for-bit.

## 6. Current finite benchmark suite

`CanonicalClosedLoopBenchV2.agda` contains exact theorem fixtures for:

```text
Jumanji Knapsack
Jumanji Maze-v0 projection
Jumanji LevelBasedForaging-v0 projection
Gymnax MetaMaze projection
Gymnax FourRooms projection
Gymnax Pong-misc projection
Gymnax MemoryChain-bsuite projection
Gymnax DiscountingChain-bsuite projection
Gymnax CartPole projection
Gymnax Bernoulli-Bandit-misc projection
Pobax RockSample projection
```

The finite projections are intentionally deterministic so they remain within the canonical import surface. Some upstream environments have stochastic generation, random keys, continuous observations, floating-point dynamics, or autorestart semantics. The Agda ports are therefore explicit finite structural projections.

For example, the current CartPole projection has discrete position updates and zero reward. Its successful completion of a fixed diagnostic horizon is not equivalent to balancing a physical CartPole.

The current FourRooms execution path still uses the finite Maze transition type. `CanonicalFaithfulGameVariants.agda` separately records the fixed FourRooms connectivity predicate. A full upstream-faithful FourRooms transition remains a distinct task.

## 7. Munchausen status

`CanonicalNegativeMunchausenTheory.agda` and `CanonicalMunchausenAblation.agda` define the current finite negative-Munchausen surface.

The intended mathematical relationship is:

```text
negative scale = sign flip of standard scale
```

The finite q-log carrier replaces transcendental logarithms with the existing finite `FiniteRational` code. The current learner still does not consume this q-log term inside the canonical critic target. Therefore the repository does not call the existing finite module a complete implementation of the published q-Munchausen algorithm.

The maintained ceteris-paribus test compares the same finite bandit and quantized CartPole environment with the no-Munchausen and negative-Munchausen reward adapter. Equal return in a fixture is an exact finite result, not a general performance conclusion.

The literature reference is Zhu, Chen, Uchibe, and Matsubara, `q-Munchausen Reinforcement Learning`, arXiv:2205.07467:

https://arxiv.org/abs/2205.07467

That paper motivates q-logarithms because ordinary logarithms mismatch Tsallis/sparsemax entropy. Its numerical and statistical benchmark conclusions do not transfer automatically to this finite Int8 learner.

## 8. CNN theorem stack

The old phrase `CNN/log-pyramid equivalence` was too strong.

The minimum useful exact composition is now:

```text
CNN code C
  -> decode : C -> A
  -> CNN-side transition : C -> C
  -> learner-side transition : A -> A
  -> commute proof
       decode(cnnStep c) = learnerStep(decode c)
```

From that one commuting law, `CNNTransitionBisimulation.agda` proves:

```text
same decoded representation
        => same learner transition
        => same decoded representation after one step
        => same decoded representation after n steps
```

This is an exact finite-state transition preservation/bisimulation schema. Its practical payoff is direct: once a CNN encoder/decoder implementation satisfies the one commuting theorem, its recurrent behavior can be substituted without reproving the entire learner trajectory theorem at every time horizon.

It is not a bijection between arbitrary CNNs and the learner, not an approximation theorem, and not a function-class separation result.

A stronger CNN theorem would need an explicit CNN definition with layer types, spatial domain, convolution kernels, pooling/stride semantics, parameter constraints, and either exact equality or a declared approximation metric. The repository deliberately does not smuggle such an external CNN standard into the learner monolith.

## 9. Finite functional completeness

`FiniteParameterCompleteness.agda` proves exact table completeness:

```text
for every f : Fin n -> Fin m,
there exists a finite parameter table representing f exactly.
```

This is finite functional completeness of parameter slots. It is not universal approximation over unrestricted real-valued functions.

The current explicit arithmetic carrier can express finite-domain polynomial-like and piecewise arithmetic functions, threshold/sign behavior, and finite rational encodings. No transcendental primitive is part of the maintained learner signature.

## 10. Norm pair and path norm

The maintained finite norm file defines explicit scalar examples of

```text
L1 weight magnitude
1-path magnitude
```

with componentwise Nat ordering and finite product deductions.

The paper `Hidden Synergy: L1 Weight Normalization and 1-Path-Norm Regularization` concerns PSiLON-style MLPs and related residual blocks. Its Lipschitz and generalization results do not automatically apply to this learner's GRU + sparsemax + Walsh composition.

The repository therefore does not claim that the current `NormPair` is a formal implementation of the PSiLON path norm, nor that its published bounds transfer to the learner.

## 11. Hard sparsity

`hardSparse-composition-normPair-F4-L2` proves the strongest unconditional local result presently justified:

```text
HardSparse(policy)
  -> HardSparse(policy after NormPair/F4/L2 state replacement)
```

This is policy invariance under specified state replacement. It is not a trajectory-wide sparsity theorem and not an arbitrary-state approximation theorem.

## 12. Exact trajectory rank

The exact learner rank is

```text
V(s) = clock s
```

with

```text
V(fullStep K s) = V(s) + 1
V(iterate K n s) = V(s) + n
```

This is an increasing Nat rank, not a decreasing classical Lyapunov function. It excludes fixed points and finite cycles by direct Nat contradiction. No environmental, statistical, reward-distribution, or asymptotic assumption is involved.

## 13. External benchmark references

### CleanRL

CleanRL describes itself as a single-file implementation library and documents classic-control PPO/DQN commands and benchmark infrastructure across 7+ algorithms and 34+ games.

https://github.com/vwxyzjn/cleanrl

### Gymnax

Current Gymnax README reports, among other entries, a CartPole-v1 PPO/ES checkpoint return of 500, FourRooms-misc checkpoint return of 1, MemoryChain-bsuite checkpoint return of 0.1, and DiscountingChain-bsuite checkpoint return of 1.1, together with displayed A100 throughput figures.

https://github.com/RobertTLange/gymnax

These are upstream JAX environment reports. They are not direct numerical baselines for the deterministic finite Agda projections unless environment and learner semantics are matched.

The precise external reference ledger is maintained in `docs/BenchmarkReferenceLedger.md`.

## 14. GameTheory and Econlib boundary

Game-theory ports remain individual modular files. They are not imported into `CanonicalLearnerMonolith.agda`.

`GameTheory.agda` now has its own finite Int8 carrier and no `efficient_chad.Int8` dependency.

`Equilibrium.agda` is likewise detached from EfficientCHAD.

`MatchingPennies.agda` is an independent finite theorem fixture.

The learner can therefore be checked against these games without embedding them in learner state or learner transition definitions.

## 15. Pruned redundancy

Verified redundant files removed from the canonical branch include:

```text
CheckFiniteAlgebra_v147.agda
CheckQProjection_v147.agda
CheckQTerminal_v147.agda
efficient_chad/Int8.agda
Exploration/Generated/ExplorationCandidates.agda
GRUCompositionAlgebra.agda
MobiusGroup.agda
MobiusRational.agda
MobiusSemidirectCycleComposition.agda
SparsemaxCriticWatkins.agda
SparsemaxCriticWatkins_test.agda
```

Pruning is based on repository-local dependency closure, not filename style.

## 16. CI authority

The main branch workflow is `.github/workflows/agda.yml`.

It now checks:

```text
canonical monolith
closed-loop interface + regression
closed-loop benchmark suite
game ports + faithful variants
finite parameter completeness
finite norm algebra
control/observability
CNN preservation + factorization + transition bisimulation
negative-Munchausen theory + ceteris-paribus regression
GameTheory + Econlib + MatchingPennies
```

The current main run after the latest synchronization is the acceptance oracle. A theorem or benchmark result is not treated as accepted until that current-head Agda run succeeds.

## 17. Replication rule

Use `d = 64`.

Keep the learner monolith environment-free.

Keep games external.

Do not enlarge the direct import surface unless a proof term actually requires a module unavailable in the current eight-module closure.

Do not turn structural adapter tests into claims of general-A sparsemax, full upstream environment equivalence, universal approximation, CNN expressivity separation, control-theory controllability, or statistical learning superiority.
