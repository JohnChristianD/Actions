# Fresh Sparsemax Watkins Finite-Cycle Theorem Plan

Goal: make the fresh baseline actor-free and direct-critic only, then prove exactly which component ablations retain the unconditional finite-cycle exclusion theorem.

## Architecture

`SparsemaxCriticWatkins` is the sole learned policy source. Sparsemax is a deterministic policy projection. Watkins supplies the learner/trace family. Actors and non-Watkins critic families are permanently retired from this line.

## Mutable actor versus pure direct critic

A mutable actor on an invariant graph has an enlarged state `(critic, actor)` and a separately stored actor update. It is equivalent to direct Watkins only on the invariant graph `actor = actorOf critic`, when the actor update commutes with the critic update and reproduces the same sparsemax policy. The actor therefore contributes extra state variables and an extra transition channel outside that graph. A pure direct sparsemax-Watkins learner has no such actor coordinate at all. The earlier actor two-cycle was therefore a counterexample to unconditional equivalence of arbitrary mutable actor dynamics, not evidence that direct Watkins itself cycles.

## The theorem source

The finite-cycle theorem must come from the actual deterministic learner transition, not from a detached certificate supplied as an assumption. On a finite carrier, the desired endogenous condition is a concrete `Nat` potential `E` with

`step s ≢ s -> E (step s) < E s`.

The current `WholeCriticWatkinsLyapunov` and connected GRU records are theorem schemas, not yet concrete unconditional proofs. Until an actual Watkins update and its concrete `E` are defined and checked by `agda --safe`, no global finite-cycle exclusion claim is permitted.

For the fresh baseline, the strict source should be the critic state/update itself. GRU recurrence, semidirect/Mobius representation, optimizer state, L2, path norm, L1 norm, nonlinearity, recurrence, finiteness, and boundedness do not imply the strict inequality. Product components can be invariant or non-increasing, but they cannot create strictness by themselves.

## Ablation status

- Sparsemax policy projection: **not** a cycle-exclusion theorem.
- Watkins traces: **not** a cycle-exclusion theorem by themselves.
- Optimistic initialization: **not** a global cycle-exclusion theorem.
- **Pessimistic initialization is the only initialization track to use in future algebraic proofs.** It changes the starting state only; it does not strengthen a global theorem by itself.
- No-noise deterministic dynamics: **not** a cycle-exclusion theorem.
- Xorshift/support coverage: **coverage only**, not convergence.
- A different nonlinear recurrent activation: inherits the theorem **only if** the actual strict finite-state inequalities are re-proved for that activation.
- Negative signed generalized-log modifier: **not** a theorem until it is actually composed into the Watkins critic update and the resulting transition receives its own concrete strict potential proof.

Changing only initialization changes the starting state, not the global transition map. Therefore initialization cannot manufacture global cycle exclusion.

## Pessimistic negative signed generalized-log composition

Use the pessimistic initialization track throughout this composition because the existing finite signed-log module already maps its negative-log default to `pessimisticInit`.

The composition target is one critic-side transition:

`pessimistic critic state -> Watkins trace/update -> negative signed dyadic generalized-log modifier -> next critic/trace state`.

Required theorem work:

1. Define the modifier as part of the actual critic update rather than as a detached algebraic constant.
2. Define the complete finite transition including pessimistic initialization.
3. Derive a concrete critic-native `Nat` potential from the resulting state/update.
4. Prove the potential is non-increasing for every transition.
5. Prove strict decrease on every nonfixed transition.
6. Derive the finite-cycle exclusion theorem directly in `--safe` Agda.

Until steps 1–6 are machine-checked, call the track a finite algebraic composition only, not a finite-cycle theorem.

## Connected compositions that retain unconditionality

The only compositions that retain the unconditional finite-cycle theorem are those whose **actual complete transition** still has a machine-checked strict finite potential. In particular:

- direct sparsemax-Watkins + pessimistic initialization: retains the theorem **only after** the concrete critic proof is instantiated; initialization itself is neutral;
- direct sparsemax-Watkins + pessimistic negative signed generalized-log: retains the theorem **only if** the composed critic transition has its own concrete strict proof;
- direct sparsemax-Watkins × GRU: retains the theorem only if the critic or GRU transition is actually strict and every other connected component is non-increasing;
- adding invariant optimizer/L2/path/L1 state: can preserve the theorem because invariant terms contribute zero change;
- replacing activation: preserves the theorem only when the replacement's actual transition re-proves the strict inequalities;
- adding any independently mutable actor state: does **not** preserve unconditionality unless that extra state is removed or an invariant-graph reduction is proved and the theorem is then stated on that graph rather than the enlarged unconstrained state.

Sparsemax, Watkins traces, recurrence, regularization, and finite state space alone never receive cycle-exclusion credit.

## Concrete work

### Direct critic

Instantiate `SparsemaxCriticWatkinsKernel` with a real finite deterministic update, define a critic-native `Nat` rank/distance from the actual update, and prove strict decrease on every nonfixed transition. Only then instantiate `wholeCriticWatkinsNoNontrivialFiniteCycle` as a theorem about that concrete learner.

If the concrete update admits a nontrivial finite cycle, the theorem must fail. Do not patch it by introducing an external certificate.

### Connected GRU

Keep the connected critic × GRU product theorem as a composition theorem. Its strictness must come from an actually changing component. Invariant optimizer/L2/path/L1 contributors remain neutral terms.

### Coverage

Keep xorshift coverage as a separate reachability theorem. Do not infer fixed-point convergence from finite coverage.

### Game theory provenance

Keep only the Econlib examples actually sourced from `danlyng/Econlib`: Matching Pennies and Prisoner's Dilemma. Do not add unsourced game examples merely to enlarge the folder.

### Permanent pruning

Deleted and path-banned:
- `Exotic/ERL/FullCoupled/SharedActorCritic.agda`
- `Exotic/ERL/FullCoupled/SparsemaxActorVsCriticTheorem.agda`
- `Exotic/ERL/FullCoupled/SparsemaxActorVsCriticTheorem_test.agda`
- retired NoisyNet source family
- retired flatDyadic mixture sources
- unsourced redundant `Exotic/econlib/RockPaperScissors.agda`
- unsourced redundant `Exotic/econlib/RockPaperScissors_test.agda`

The canonical CI gate must reject reintroduction and must finish with a fresh successful run before the theorem stack is called passing.
