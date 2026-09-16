# Benchmark Reference Ledger

## Repository benchmark semantics

All Agda benchmark records are exact reductions of deterministic finite environment projections. They record:

- return
- reference return
- regret = reference return minus-or-truncated-at-zero
- success
- executed environment steps

They are theorem outputs, not sampled statistical estimates.

## CleanRL reference

CleanRL describes itself as a single-file implementation library and documents classic-control runs such as `ppo.py` and `dqn.py` on CartPole. Its README also links a benchmark site with 7+ algorithms and 34+ games.

Current reference:
https://github.com/vwxyzjn/cleanrl

The repository's documented benchmark configuration should be matched by algorithm, environment version, seed, timestep budget, and metric before any numerical comparison is called like-for-like.

## Gymnax reference

Gymnax provides functional JAX environment transitions and reports baseline checkpoint returns and throughput figures in its current README. The current README reports, among other entries:

- CartPole-v1: PPO/ES checkpoint return 500; 0.05 seconds per million environment steps in the displayed A100/2k-environment table.
- FourRooms-misc: PPO/ES checkpoint return 1; 0.07 seconds per million steps in the displayed table.
- MemoryChain-bsuite: PPO/ES checkpoint return 0.1; 0.13 seconds per million steps.
- DiscountingChain-bsuite: PPO/ES checkpoint return 1.1; 0.06 seconds per million steps.

Current reference:
https://github.com/RobertTLange/gymnax

These values use Gymnax's upstream stochastic, floating-point, JAX environment semantics. They are context, not direct targets for the deterministic finite Agda projections.

## q-Munchausen reference

Zhu, Chen, Uchibe, and Matsubara, `q-Munchausen Reinforcement Learning`, arXiv:2205.07467.

https://arxiv.org/abs/2205.07467

The paper explains that conventional Munchausen adds the logarithm of the current stochastic policy to the reward and that this mismatches Tsallis/sparsemax structure. Its q-log/q-exp correction restores the entropy-family alignment. The current Agda learner uses a finite rational q-log carrier rather than real transcendental logarithms; the finite negative-Munchausen module therefore proves only the sign-flip and finite-code properties currently defined in the repository.

## Comparability rule

A benchmark result is directly comparable only when environment transition semantics, observation encoding, action semantics, reward scale, termination/truncation rules, discounting, learner update equations, hyperparameters, training budget, and randomization protocol match. Otherwise record the number as a structural test or reference datum, not as an algorithmic performance comparison.
