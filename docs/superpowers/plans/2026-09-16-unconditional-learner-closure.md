# Unconditional Canonical Learner Closure Implementation Plan

Authority: `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda` plus the synchronized replication wiki.

## Closed theorem surface

- [x] Environment-agnostic Watkins/LCB/sparsemax/negative-q-log/attention/Walsh/hard-sign-Möbius-GRU/F4-L2/NormPair learner.
- [x] Persistent-GRU quotient and transition-action endomorphism monoid.
- [x] Associative GRU and Möbius-labelled scan laws.
- [x] Exact H4 Int8 Gram law `H4 H4ᵀ = 4I (mod 256)`.
- [x] Power-of-four width witness.
- [x] Full stored Int8 accounting including F4 and NormPair: 23 scalar coordinates.
- [x] Width-`d` bookkeeping: `d + 22` stored Int8 coordinates under scalar persistent layout.
- [x] NormPair/F4/L2 hard-sparsity structural invariance theorem.
- [x] Exact Nat rank `V = clock`, unit increment, fixed-point and finite-cycle exclusion.

## Width and algebra

- [x] Replication default `d = 64`.
- [x] `FiniteParameterCompleteness.agda` proves `64 = 4^3` and finite function-table completeness.
- [x] Effective learner theorem algebra documented below ring level: finite data, Nat arithmetic, equality/negation, products, and endomorphism composition.
- [x] Canonical learner remains on eight direct standard-library imports.
- [x] `FiniteNormAlgebra.agda` defines exact finite two-weight L1 and 1-path norms with componentwise Nat order and zero-product deductions.
- [x] Explicitly separated those finite definitions from the PSiLON/Hidden-Synergy theorem hypotheses. No theorem is claimed for the current GRU+sparsemax composition without matching hypotheses.

## Reachability and observation

- [x] `CanonicalControlObservability.agda` defines finite-step reachability along the canonical transition.
- [x] Every canonical forward-orbit point is proved reachable by its iterate count.
- [x] A deliberately weak orbit-controllability predicate is proved because no external control input exists in the learner state machine.
- [x] Full-state observation is injective and clock observation preserves the exact `clock + n` iterate law.
- [x] No Kalman/nonlinear steering, practical-control, environment controllability, or sensor-identification theorem is claimed.

## Environment replication

- [x] Finite executable ports for Jumanji Knapsack, Maze, LevelBasedForaging.
- [x] Finite executable ports for Gymnax MetaMaze, FourRooms, Pong, MemoryChain, DiscountingChain, CartPole, Bernoulli Bandit.
- [x] Finite executable Pobax RockSample projection.
- [x] Exact fixed Jumanji Toy Maze connectivity predicate.
- [x] Exact Gymnax FourRooms 13x13 connectivity predicate.
- [x] Explicitly distinguish deterministic finite projections from upstream stochastic/continuous numerical implementations.

## Learner execution and closed loop

- [x] The previous reward-injection regression is retained as a theorem-level diagnostic.
- [x] `learnerRewardStep-reward-insensitive` proves that changing the injected reward does not change `canonicalFullStep`: the old integration harness was not reward-learning.
- [x] `encodeActionReward`/`decodeAction` and `decodeReward` are exact finite round trips.
- [x] `closedLoopCriticUpdate` supplies the missing action-conditioned critic interface and uses a finite TD target `r + 1/2 max Q`.
- [x] `closedLoopStep` feeds the selected action and environment reward into the critic, attention signal, GRU input, optimizer input, and action-count memory.
- [x] The closed-loop bench records total return, reference return, regret-as-reference-gap, success, and environment step count.
- [x] Exact finite bench cases are instantiated for Knapsack, Maze, MetaMaze, FourRooms, CartPole, and both Bernoulli two-arm configurations.
- [ ] The closed-loop transition is an explicit action-conditioned completion of the existing interfaces, not a claim that the original autonomous `canonicalFullStep` already implemented this transition semantics.
- [ ] The `closedLoopTarget` is TD-style but is not yet a faithful implementation of a standard negative-Munchausen target-network DQN update; the existing `negativeFiniteQLog8` is not consumed by the critic update.
- [ ] Upstream empirical convergence/sample-efficiency claims remain unmade until the finite projection and learner head match the reference environment/action-space semantics.

## CNN/log-pyramid preservation

- [x] `CNNLogPyramid64` explicit 64-index representation.
- [x] `cnnToAttention` decoder and induced equivalence relation are explicit and prove reflexivity/symmetry/transitivity.
- [x] GRU-input preservation under equal decoded attention state.
- [x] Commuting theorem from a decoded pyramid representation into the existing `canonicalGRUStep`.
- [ ] No bijection with an arbitrary CNN architecture is claimed.
- [ ] No approximation metric or error bound is claimed.
- [ ] No function-class separation from fixed-depth CNNs is claimed, because no competing CNN class/metric has been defined.

## GameTheory and pruning

- [x] `GameTheory.agda` remains an external modular theorem/test surface and now uses seven direct standard-library imports with no `efficient_chad.Int8` dependency.
- [x] Current learner monolith does not import GameTheory.
- [x] Prisoner’s Dilemma pure-Nash, best-response, stabilization, and finite iteration proofs remain explicit.
- [x] `MR15Reachability`, `OpenESDyadic`, and `NoisyNetCoupled` are absent from the canonical branch.
- [x] Broken v147 interpolation/trigger/wake marker files and the old three-file exploration schema/counterfactual cluster were pruned.
- [ ] Remaining legacy repository tooling is retained unless a zero-user audit proves it is safe to delete; CI synchronization scripts are not pruned merely because they are old.

## Synchronization

- [x] Forbidden-theorem scanner covers learner, game ports, faithful map variants, completeness, finite norm algebra, control/observability, CNN preservation, execution regression, GameTheory, and generated report.
- [x] Haskell theorem generator checks all maintained theorem surfaces and runs Agda safe checks.
- [x] Workflow compiles all maintained Agda surfaces before generation.
- [x] Replication wiki synchronized to d64, finite functional completeness, finite norm definitions, formal control vocabulary, game ports, CNN preservation, state accounting, exact Nat rank, and pruning boundaries.
- [x] Main-branch pushes, PRs, hourly schedule, and manual workflow dispatch use the same canonical verification path.

## Acceptance

The active PR is `#36`, branch `agda-theorem-first-monolith-20260916`. The current head is being checked by workflow run `2275` (`35086935199`). Do not mark the branch green until current-head canonical Agda, ports, faithful maps, parameter completeness, finite norm algebra, control/observability, CNN preservation, GameTheory, learner execution regression, generator, redundancy audit, and generated report all pass.