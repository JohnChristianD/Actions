# Deterministic QSA monolith

## Scope

`Exotic/ERL/FullCoupled/DeterministicQSA.agda` is the canonical theorem monolith. The source is intended to be environment-agnostic: it does not quantify over rewards, transition probabilities, observations, action spaces, environments, random variables, estimators, replay buffers, target networks, or asymptotic statistical limits.

The theorem contracts are instead stated over an arbitrary state type, an arbitrary deterministic step function, or an arbitrary support relation. A named QSA certificate is only a record packaging these mathematical premises. The name does not assert that any particular learning algorithm instantiates the certificate.

## Self-contained surface

The canonical file defines its own `Nat`, propositional equality, bottom, negation, sum, natural-number `<` and `≤`, reachability, decidable equality contracts, iteration, fixed points, Lyapunov certificates, convergence records, support-Lyapunov certificates, and all helper lemmas needed by its main theorems.

No external Agda module is required by the canonical theorem source. `--safe` remains enabled.

## Deterministic theorem family

`eventuallyFixedFromLyapunov` proves finite-time arrival at a fixed state whenever a natural-valued energy strictly decreases at every nonfixed step and state equality is decidable.

`deterministicQSAStyleConvergence` strengthens this with a unique-fixed-point certificate. Every initial state reaches the distinguished target after a finite number of iterations, with an explicit equality proof.

`deterministicQSAStyleTargetFixed` extracts the target's fixed-point proof from the certificate.

`deterministicQSAStyleFixedStatesCollapse` proves that every fixed state equals the distinguished target.

`deterministicQSAStyleNoNontrivialCycle` rules out every finite return from a nonfixed state under the Lyapunov premise.

## Support theorem family

`SupportLyapunov` assigns a natural-valued support energy and requires strict decrease on every supported off-diagonal edge.

`noStrongSupportLyapunovTwoCycle` proves that mutual supported edges between distinct states are incompatible with this strict decrease law.

`ClosedSupportOrbit` encodes a finite closed supported orbit directly as a natural-indexed path. It requires a supported edge and an off-diagonal proof at every path position, together with a final equality returning to the initial state.

`closedSupportOrbitImpossible` proves that such a closed finite orbit cannot exist under a strict support-Lyapunov law. The proof is constructive: iterated `<` transitivity produces a strict self-descent of one natural number, then natural irreflexivity closes the contradiction.

`supportRelationAntisymmetricOffDiagonal` packages the two-cycle obstruction as the reusable rule

`x ≢ y -> R x y -> ¬ R y x`.

The theorem is relational, not probabilistic. “Support” means only membership in the supplied relation.

## Finite structural counterexample

The monolith contains a two-state relation with every edge supported. It has an explicit irreducibility proof, explicit self-loops, and a `PeriodOne` certificate, while `noTwoStateStrongSupportLyapunov` proves that no strict support-wide Lyapunov certificate can exist for that relation.

This separates structural recurrence properties from strict support-wide descent assumptions.

## Exact boundaries

The file proves finite, constructive consequences of explicit certificates. It does not prove that arbitrary reinforcement-learning, stochastic-process, GRU, neural-network, environment, reward, or empirical training systems satisfy those certificates.

No probabilistic conclusion follows merely from the names `QSA`, `support`, or `Lyapunov`. An application theorem must explicitly supply the relevant certificate.

## Repository maintenance

The canonical monolith is dependency-free at the Agda source level. Former helper modules are pruned only when a repository-wide reference scan establishes that they are no longer needed elsewhere. Unrelated exploration, economic, and CI modules are not silently deleted merely because the canonical theorem source no longer imports them.
