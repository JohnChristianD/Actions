# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

## Canonical composition

`E -> dyadic RoPE (Walsh-Rademacher) -> sparsemax attention -> frozen Haar -> specialized recurrent GRU -> Pi`.

The old standalone pointwise activation/MLP path is retired. The only retained nonlinear representation operations are the GRU's internal gates:

`z = 0.5 * (1 + softsign)`
`r = 0.5 * (1 + softsign)`
`h~ = signReLU`.

The GRU is recurrent, not an MLP merely repeated by convention. Its finite window actions compose associatively; finite sequential actions therefore admit exact scan/reassociation theorems.

## Transformer-like classification

The front half has the structural ingredients needed for a finite Transformer-like composition theorem: positional action, sparse attention, and frozen linear mixing. The whole architecture is a hybrid recurrent attention composition, not a literal claim of identity with a Transformer implementation. A task-agnostic expressivity theorem requires an explicit carrier-lifting theorem from the attention representation into the recurrent state and is therefore stated separately.

## Log-pyramid hierarchy

A log-pyramid theorem requires an explicit hierarchy of context windows or scales, together with a refinement/coarsening map between adjacent levels. The recurrent scan theorem supplies associative window composition but does not by itself prove logarithmic depth. The canonical target is an adaptive window schedule whose composition tree has logarithmic height and whose restriction/refinement maps commute with the sparsemax/Haar/GRU transition.

## GRU perturbation methods

`GRU-OpenES`, `GRU-MR15`, and `GRU-NoisyNet` remain the actual perturbation-method family. The probability law is a separate parameter of each method.

A standard GRU has six affine matrices. Exploration is restricted to the three recurrent matrices `U_z`, `U_r`, and `U_h`; input-side matrices are not perturbed. For hidden width `d`, the persistent recurrent noisy carrier contains `3*d^2 + d` Int8 coordinates before optimizer and auxiliary state.

No strict method ordering is admitted unless Agda proves method-specific projection, lift/section, retraction, and proper-fiber theorems on the *full coupled carrier*. A common witness bundle is not a strict ordering theorem.

## Global optimization boundary

The optimizer and global L2 regularization are always global to every learned component. No local exception is introduced for the GRU, sparsemax-adjacent learned maps, actor, or critic.

The canonical optimizer remains `standardTDLambdaInt8`. Global coupling records must quantify over the complete learned parameter state, including actor, critic, recurrent matrices, and any learned attention parameters.

## Norm-pair boundary

Only genuinely learned nonlinear/attention operators retain their local L1/path-one norm-pair obligation. Frozen Haar does not acquire a learnable norm-pair obligation. If sparsemax is fixed, its norm-pair is pruned; if sparsemax is learned, its norm-pair remains part of the theorem interface.

## Möbius recurrence and scan

The internal GRU gates are expressed through finite dyadic `softsign` and `signReLU` operations. Pointwise Möbius witnesses compose sequentially at the actual intermediate value; the theorem is pointwise in the recurrent state and never replaces the entire recurrent map by one unsupported global Möbius map.

The finite recurrent window action forms an associative composition algebra. A parallel scan theorem follows once the concrete GRU update is given a homogeneous finite action witness. The scan theorem establishes reassociation and parallel-precomputation correctness, not a performance claim.

## Flat Dyadic law

Flat Dyadic is the sole active probability law. Its finite mass is constant across the 256 Int8 residues. Its algebraic specialness comes from exact full support, exact normalization, positive zero/self-loop support, and positive unit-step support. Those facts make the finite communication and aperiodicity witnesses collapse cleanly.

Unimodality is secondary here. Uniformity implies weak and strong finite-profile monotonicity predicates that are useful as derived corollaries, but neither is the source of the reachability theorem. No environment-dependent distribution comparison is admitted.

## Actor-critic boundary

The actor and critic are finite Int8 functions. The deterministic-policy-gradient theorem is expressed as an exact finite chain-rule/CHAD theorem over the declared actor/action carrier rather than importing a continuous-action result by name.

The critic target retains the declared max-bootstrap operator. A full coupled actor-critic theorem requires exact proofs for actor transport, critic target transport, optimizer/L2 coupling, and composition with the recurrent representation. Jensen or local max inequalities alone do not certify the whole coupling.

## Endogenous theorem frontier

The active theorem generator should emit only full-composition propositions of the form

`FullCoupled(method, flatDyadic, representation, optimizer, L2, actor, critic)`.

Subtheorems for law normalization or local gate identities are admissibility premises, not final theorem candidates. Every final candidate is checked by `agda --safe`.

The desired strict-strength ordering is a logical implication order on theorem records, not a statistic:

`T_OpenES  <  T_MR15  <  T_NoisyNet`

only after explicit carrier maps establish strict factor extensions. The recurrent GRU class is a separate stronger-structure candidate. A theorem `T_NoisyNet -> T_GRUNoisyNet` requires an actual projection/lift/retraction from the old coupled carrier into the recurrent carrier.

## Algebraic expressivity classification

The architecture is task-agnostic in the finite algebraic sense: all operators act on finite Int8 carriers and compose exactly. It should be called `quantized Transformer-like + recurrent state-space composition`, not a generic universal approximation theorem. Unbounded kuya terminology replaces limiting terminology in the specification: recurrent depth and window depth may be unbounded in the specification, while every checked theorem instance is finite.

## Runtime/toolchain pruning

The mathematical authority surface contains Agda `--safe` plus only the existing minimal support needed by the repository's theorem generator. No extra proof library is required for the finite dyadic results. Python/Ruby/Elixir/Erlang/Clojure/CMD/Bash-style runtime logic is not part of the mathematical authority. Pull requests remain GitHub delivery objects, not mathematical dependencies. No active Nix source dependency is present on this branch; Guix is therefore not required. Where a reproducible environment is needed later, pin one declarative environment rather than maintaining two competing package-manager authorities.

## Validation boundary

The representation primitive gate is green for commit `3382f71eb2e36f7d6839daae563f3acfb03d6f4e`; the canonical Agda gate for that same commit was still failing. Therefore repository-wide green status is not yet claimed. The next accepted head must show the canonical Agda `--safe` workflow passing before the PR is treated as complete.

No empirical performance theorem, environment-conditioned statistical ranking, or external mathematical library becomes an acceptance oracle.
