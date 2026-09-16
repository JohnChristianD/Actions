# Deterministic theorem monolith

## Canonical source

`Exotic/ERL/FullCoupled/DeterministicQSA.agda` is the canonical self-contained theorem source. It is checked with `{-# OPTIONS --safe #-}` and has no Agda imports.

The source therefore does not depend on a separately defined environment, reward process, probability space, observation kernel, action type, neural architecture, optimizer implementation, replay mechanism, target network, estimator, or statistical limit.

The identifier `DeterministicQSAStyleCertificate` is only a mathematical packaging record. It does not assert that a particular reinforcement-learning implementation satisfies the record.

## Definitions included in the monolith

The file defines its own natural numbers, propositional equality, substitution, contradiction, negation, constructive sum, natural-number `<` and `≤`, decidable-equality certificates, iteration, fixed points, natural Lyapunov certificates, exact finite convergence records, support relations, reachability, irreducibility, self-loops, period-one certificates, support-Lyapunov certificates, and the finite structural counterexample.

No external theorem module is required by the canonical source.

## Deterministic results

`eventuallyFixedFromLyapunov` proves finite-time arrival at a fixed state from three explicit premises: a deterministic step function, decidable state equality, and a natural-valued energy that strictly decreases on every nonfixed step.

`deterministicQSAStyleConvergence` adds a unique-fixed-point certificate and proves exact finite convergence of every initial state to the distinguished target.

`deterministicQSAStyleTargetFixed` extracts the target fixed-point proof.

`deterministicQSAStyleFixedStatesCollapse` proves that any fixed state equals the distinguished target.

These are constructive finite theorems. They do not infer that an arbitrary learning system possesses the required certificates.

## Support results

`SupportLyapunov` gives a natural-valued energy for an arbitrary binary support relation and requires strict energy decrease on every supported off-diagonal edge.

`noStrongSupportLyapunovTwoCycle` proves that two distinct states cannot support edges in both directions under such a certificate.

`ClosedSupportOrbit` encodes a finite closed supported orbit using only a natural index, an edge proof at each index, off-diagonal proofs, and a closing equality.

`closedSupportOrbitImpossible` proves that a strict support-Lyapunov law cannot coexist with such a closed finite orbit. The proof composes strict natural-number inequalities until it obtains `E < E` and closes the contradiction with natural irreflexivity.

`supportRelationAntisymmetricOffDiagonal` exposes the reusable off-diagonal consequence

`x ≢ y -> R x y -> ¬ R y x`.

No probability semantics are attached to the word “support”. It denotes membership in the explicitly supplied relation.

## Structural counterexample

The monolith defines a two-state relation whose every edge is supported. It has explicit irreducibility, self-loop, and period-one proofs. The theorem `noTwoStateStrongSupportLyapunov` proves that this relation cannot admit the strong support-wide strict Lyapunov certificate.

This demonstrates that recurrence properties and strict support-wide descent are separate assumptions.

## What is not claimed

The monolith does not establish statistical convergence, almost-sure convergence, expected convergence, asymptotic rates, reward optimality, environment-specific properties, neural-network properties, GRU properties, or properties of any empirical training run.

Any application must instantiate the generic state, step, equality, relation, Lyapunov, and terminal certificates explicitly.

## Pruning policy

`.ci/prune-monolith-redundancies.py` performs a repository-wide Agda import scan. A candidate file is deleted only when its declared module is no longer imported anywhere else. This prevents consolidation of the canonical source from silently breaking unrelated exploration or economic modules.
