# Canonical closed-loop benchmark

## Formal interface

`Exotic/ERL/FullCoupled/CanonicalClosedLoopBench.agda` defines a finite deterministic benchmark interface:

`ClosedLoopSpec N S` contains the environment state, finite horizon, reference return, learner-state action selection, environment-action-to-learner-action projection, deterministic environment step, and success predicate.

`runClosedLoop` executes the closed loop:

`learner state -> environment action -> environment transition -> reward -> CanonicalLearner closedLoopStep -> next learner state`

`ClosedLoopMetrics` records:

- `totalReturn`
- `referenceReturn`
- `regret = referenceReturn ∸ totalReturn`
- `success`
- `steps`

This is a finite theorem/normalization harness. It is not a stochastic runtime benchmark and does not silently stand in for floating-point JAX or Jumanji execution.

## Current modular game fixtures

CartPole, Bernoulli Bandit, Knapsack, Maze-v0 projection, MetaMaze, FourRooms, LevelBasedForaging, Pong-misc, MemoryChain, DiscountingChain, and RockSample each remain separate environment definitions in `CanonicalGamePorts.agda` and are passed into the generic interface.

The learner monolith does not import these games.

## Learner kernel boundary

`CanonicalLearnerMonolith.agda` defines `FullLearnerKernel` as an explicit parameter. The benchmark imports the concrete finite kernel fixture from `CanonicalLearnerGameExecution_test.agda` so the whole step is executable under `--safe` without introducing a hidden environment dependency.

The benchmark therefore establishes execution of the declared learner composition, not a claim that an externally pretrained policy has learned each task.

## External reference points

CleanRL currently documents its single-file PPO implementation for `CartPole-v1`, including a published benchmark value of `490.04 ± 6.12` episodic return in its PPO table. It also describes logging episodic return, episodic length, steps per second, and PPO losses.

Gymnax currently documents `CartPole-v1` with a checkpoint return of `500`, and lists reference checkpoint returns for `MemoryChain-bsuite` (`0.1`), `DiscountingChain-bsuite` (`1.1`), and `FourRooms-misc` (`1`).

These external values are reference documentation only. The Agda ports in this repository are finite deterministic projections and therefore are not numerically identified with those runtime environments. No performance comparison is asserted from the formal records alone.

## Reproduction command

Use the repository CI workflow with Agda 2.8.0 and standard library 2.4. The workflow checks the canonical monolith, all maintained environment ports, the closed-loop benchmark, negative-Munchausen theory, CNN preservation, finite completeness, finite norm algebra, and the GameTheory/Econlib fixtures.
