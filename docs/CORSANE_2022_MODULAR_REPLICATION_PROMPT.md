# Corsane-2022-style modular replication contract

Use this contract as the reproducibility boundary for the current Exotic ERL proof-and-experiment system.

## 1. Authority and architecture

Treat Agda `--safe` kernel checking as the mathematical authority. Do not replace a failed kernel proof with a passing external oracle.

Use the modular proof DAG as the primary architecture:

1. `Exotic/ERL/Stages/Stage01_FiniteAlgebra.agda`
2. `Exotic/ERL/Stages/Stage02_CHAD.agda`
3. `Exotic/ERL/Stages/Stage03_LinearLearner.agda`
4. `Exotic/ERL/Stages/Stage04_QProjection.agda`
5. `Exotic/ERL/Stages/Stage05_Representation.agda`
6. `Exotic/ERL/Stages/Stage06_CoupledLearner.agda`
7. `Exotic/ERL/Stages/Stage07_OuterFinite.agda`
8. `Exotic/ERL/Stages/Stage08_Integration.agda`

The monolithic `Exotic/ERL/FullCoupled/CompleteSafe_v147.agda` is a compatibility/regression artifact and must never be treated as the sole modular source of truth.

## 2. Mathematical semantics

Keep the learner components distinct because each contributes a separate compositional boundary:

- finite algebra;
- CHAD primal/reverse map;
- linear critic and finite TD replay;
- exact finite q-projection;
- representation boundary and finite VJP;
- coupled learner with L2 coupling;
- finite CVT archive;
- integration certificate connecting all preceding boundaries.

Preserve finite constructive proofs. Do not introduce real-analysis convergence claims merely to close a finite theorem.

Preserve the q-projection algebra, finite replay, finite trace/state transitions, coupled L2 semantics, and exact representation boundary. Do not weaken a theorem to obtain a parser or CI pass.

## 3. Evolutionary semantics

There is exactly one evolutionary layer in the active semantics:

`fixed-centroid CVT-MAP-Elites archive + OpenES emitter`.

Do not add other evosax strategies to the Agda semantics. QDax may be cited as a runtime/ecosystem reference only; it is not an additional evolutionary layer.

The active archive is finite. Centroids are finite input data. Nearest-centroid assignment is finite comparison logic, not a theorem about an infinite metric space.

## 4. OpenES algebra

Retain the finite OpenES algebraic surface:

- finite antithetic pairing/summation;
- antithetic sign cancellation;
- finite estimator construction;
- explicit mean-update equation;
- composition from coupled learner fitness to estimator to archive insertion.

Do not assert global OpenES convergence, stochastic-process convergence, or infinite-horizon optimization from these finite equations alone.

## 5. Monotonicity

The retained monotonic invariant is archive-incumbent monotonicity under best-value insertion/max comparison.

Do not claim that OpenES parameter trajectories or raw fitness trajectories are monotone.

Any stronger monotonic theorem must be stated as a finite order property and proved constructively in Agda.

## 6. Repair layer

Use Python 3 on the GitHub Ubuntu runner for deterministic source normalization and syntax repair before the authoritative Agda check.

Repair scripts may:

- qualify ambiguous namespace operators;
- normalize stdlib-free notation;
- repair known generated syntax;
- normalize structurally equivalent generated bindings.

Repair scripts must not introduce axioms, postulates, unsafe features, hidden imports, theorem weakening, or semantic substitutions that change the intended theorem.

The CI runner may install Agda 2.8.0. The proof environment intentionally remains usable without the Agda standard library unless a stage explicitly requires an installed dependency.

## 7. CI gate

The reproducible gate is:

`Python normalization -> Stage01..Stage08 --safe -> optional external oracle checks -> authoritative CompleteSafe regression check`.

The staged modular checks must remain independently runnable.

The CI workflow must fail closed: a failed authoritative Agda check is a failure even when every external oracle agrees with the intended algebra.

## 8. External oracle policy

External Haskell, Scala, Swift, Rust, Elixir, Clojure, R, symbolic-CAS, or similar programs are evidence generators only.

They may:

- compute finite reference values;
- cross-check independent implementations;
- locate likely algebraic discrepancies;
- test deterministic examples;
- provide regression evidence.

They may not:

- certify an Agda theorem in place of the kernel;
- modify Agda semantics;
- introduce an unproved asymptotic theorem;
- silently substitute an alternative evolutionary algorithm.

## 9. CSV replication layout

Use a flat, rectangular Corsane-2022-style replication CSV. One row is one evaluated phenotype at one explicit replication stage.

Recommended columns, in this order:

`candidate_id,stage,parent_candidate_id,method,archive_family,emitter,representation,critic,trace_rule,q_projection,l2_coupling,munchausen,fitness_definition,seed_group,seed_count,horizon,task,task_return,td_objective,archive_coordinate_1,archive_coordinate_2,archive_incumbent,operator_contract,proof_stage,proof_status,oracle_status,provenance,notes`

Rules:

- preserve direct measured returns;
- never inflate or rescale a task return to force promotion;
- never round measured returns;
- keep genotype/configuration metadata in the same row;
- distinguish fresh measurements from historical values;
- use `NA` for unavailable external runtimes rather than proxy scores;
- record exact seed count and horizon;
- record the proof stage and kernel/oracle status independently.

For phenotype replication, record all active semantic switches explicitly rather than inferring them from filenames.

## 10. Promotion and tie-breaking

Do not import historical fitness into a fresh replication.

Promote only from fresh direct measurements. Use deterministic tie-breaking over the declared direct task metrics. Never turn a screening metric into the primary task return.

Keep all continuous genotype values at full precision during search. Any post-selection display rounding must be explicitly marked as presentation-only and must not alter the stored measured return or proof input.

## 11. Modular reproducibility target

A new checkout should reproduce the proof graph without needing the monolithic file to understand the architecture.

The minimal reproducible proof target is `Stage08_Integration.agda` plus its imports and the corresponding CI stage checks.

The monolithic file may remain in-tree as a regression target until it is fully closed, but new theorems should be introduced modularly and then, only when useful, reflected into the monolith.

## 12. Closure policy

For every failure:

1. classify it as parser/scope/type/termination/coverage/semantic;
2. fix the narrowest root cause;
3. rerun the affected modular stage;
4. rerun the authoritative kernel check;
5. preserve all already-passing stages;
6. do not declare closure until fresh CI evidence is green.

Never stop merely because an external implementation succeeds. The final proof authority remains Agda `--safe`.
