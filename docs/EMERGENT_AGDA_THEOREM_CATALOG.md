# Emergent Agda theorem catalog for the coupled ERL system

This catalog separates what is already kernel-proved from what is a structurally available next theorem and what still requires an explicit mathematical certificate. It is a design and replication record, not permission to claim unproved convergence or stability results.

## Authority

Agda `--safe` is the mathematical authority. The modular Stage01..Stage08 graph is the primary proof architecture. `CompleteSafe_v147.agda` remains a compatibility/regression target while it is being closed.

## Current kernel-proved structural surface

| ID | Theorem family | Current status | Kernel role |
|---|---|---|---|
| EAT-01 | finite algebra operation boundary | proved | concrete algebra agreement |
| EAT-02 | CHAD identity/composition boundary | proved | primal/pullback transport |
| EAT-03 | finite linear critic update shape | proved | critic-state boundary |
| EAT-04 | q-projection idempotence | proved | exact retraction boundary |
| EAT-05 | representation expansion boundary | proved | historical representation compatibility surface |
| EAT-06 | finite VJP transport shape | proved | reverse-map boundary |
| EAT-07 | coupled L2 state preservation | proved | critic/representation coupling state boundary |
| EAT-08 | finite archive max/insert shape | proved | incumbent composition |
| EAT-09 | integrated Stage08 certificate | proved | simultaneous coupled boundary witness |
| EAT-10 | method-preservation under outer step | proved | active-method state preservation |
| EAT-11 | finite OpenES antithetic cancellation | existing theorem surface | estimator algebra |
| EAT-12 | finite OpenES mean update equation | existing equation surface | emitter state transition |

The current Stage08 certificate requires finite algebra, CHAD, critic, q-projection, representation, coupled L2, archive, and method-preservation boundaries simultaneously. That is an integration theorem, not merely a list of independently typed declarations.

## EAT-30: LayerNorm-free CReLU + Tsallis-2 Efficient-CHAD target

The v150 target is deliberately independent of LayerNorm. Its intended forward core is affine + CReLU followed by Tsallis-2/sparsemax attention. The optimizer boundary remains standard magnitude-aware q-IDBD; parameter-direction sign is an optional ablation rather than the canonical learner.

The finite ordered structure is:

`Affine -> CReLU -> QK score -> Tsallis-2 active-set equilibrium -> weighted value sum`

with a separate learner boundary:

`IDBD direction -> q-projection -> q-IDBD update -> dyadic coupled-L2`.

The integrated certificate tracks:

- CReLU reconstruction: `cplus(x) - cminus(x) = x`;
- CReLU magnitude decomposition: `cplus(x) + cminus(x) = abs(x)`;
- Tsallis-2 equilibrium on an active set: `p_i = score_i - tau` for active coordinates and `p_i = 0` otherwise;
- finite normalization: `sum p_i = 1`;
- L1 weight witness and bound;
- two-layer 1-path-norm witness and bound;
- q-projection idempotence;
- dyadic coefficient law `lambda (k+1) + lambda (k+1) = lambda k`;
- finite branch product carrying forward, attention, and optional update sign patterns.

The intended theorem does not claim global real-analytic convergence. Sensitivity is a finite certificate over an explicit ordered algebra. External exact-Rational programs are cross-checks only; they do not upgrade an Agda theorem's proof status.

### EAT-31: branchwise polynomial degree law

For an affine+CReLU representation entering a dot-product attention stage, if the incoming branchwise degree is `d`, then:

`deg(QK) <= 2d`

and

`deg(score * value) <= 3d`.

Thus the counterfactual algebraic Transformer has the finite recurrence

`D(0) = 1`, `D(k+1) = 3 D(k)`,

so `D(k) = 3^k` as the branchwise degree upper bound, provided the attention scores and values are polynomial on the fixed finite branch. L1 and 1-path norm constraints bound coefficients/sensitivity but do not change this degree recurrence.

### EAT-32: exact sparse equilibrium / sensitivity composition target

For fixed CReLU branch and fixed Tsallis active set, the routing coefficients are affine in the scores. A sensitivity proof should therefore proceed by finite branch composition rather than a real-analysis mean-value theorem. The target is an explicit finite coefficient bound whose inputs include the representation L1 bound and 1-path norm bound and whose routing contribution is controlled by normalized nonnegative Tsallis weights.

### EAT-33: double-sign extension

If parameter-direction sign is enabled, the total finite branch state becomes

`forward CReLU branch × Tsallis active set × update-sign branch`.

The forward CReLU channels retain magnitude; the optional update sign quantizes only the q-projected parameter direction. Consequently q-IDBD is the information-preserving canonical learner, while sign-q-IDBD is a finite direction-only quotient/ablation rather than an equivalent algorithm.

## Emergent finite-horizon theorems that fit the current no-real-analysis policy

### EAT-20: finite-horizon state boundedness

Add a finite fuel/index `k` and a state bound certificate. Prove by induction that every state reached in at most `k` transitions remains below its declared bound.

Schematic form:

`Bound s B -> StepBound B C -> Reach k s t -> Bound t (IterBound k B C)`

The bound can be represented entirely by inductive finite arithmetic. No topology, limits, derivatives, or infinite trajectories are required.

### EAT-21: finite-horizon Jacobian-entry boundedness

A true Jacobian theorem requires explicit finite derivative/Jacobian data and a bound certificate. Once those are present, prove that every entry, row sum, column sum, or chosen finite norm of the Jacobian is below a finite bound by structural recursion over a finite matrix.

This is the cleanest algebraic replacement for a classical Jacobian boundedness argument. The kernel proves the finite enumeration and inequality, rather than invoking a real-analysis norm theorem.

Required new ingredients: finite matrix representation, an explicit Jacobian/VJP certificate, and a finite norm/order structure.

### EAT-22: finite-horizon sensitivity / tracking bound

Represent the one-step discrepancy recurrence as finite algebra:

`e(next x, next y) <= a * e(x,y) + b`.

Then prove the finite unrolling theorem:

`e_k <= a^k * e_0 + b * (1 + a + ... + a^(k-1))`.

This gives a genuine finite-horizon tracking bound without any limiting argument. A contractive local case can then be represented by a finite arithmetic premise such as `a < 1` in an explicitly ordered finite algebra.

### EAT-23: finite local convergence by ranking function

Use a natural-valued or otherwise well-founded finite ranking function `V`. Prove:

`not terminal s -> V(step s) < V s`.

Then finite induction/well-founded recursion proves that a terminal state is reached after finitely many steps, with an explicit bound on the number of steps.

This is stronger and cleaner than saying “converges” informally: it is a constructive local termination/convergence theorem with no real analysis.

### EAT-24: bounded coupled perturbation theorem

For coupled learner states `s` and `t`, define a finite discrepancy measure over critic, representation, q-bound, and regularization state. Prove one-step non-expansiveness or an affine recurrence under a declared coupling certificate.

This produces a direct theorem about robustness of the coupled learner, rather than separate robustness statements for critic and representation.

### EAT-25: compositional invariant preservation

Package every Stage01..08 invariant into one state predicate `Inv`. Prove `Inv s -> Inv (outerStep s)` and then derive `Inv` for every finite iteration count.

This is the natural induction closure of the existing Stage08 integration certificate.

### EAT-26: idempotent projection + archive insertion normal forms

Prove that q-projection is a retraction and that repeated projection reaches the same normal form. Separately prove archive insertion idempotence for the same candidate and deterministic max behavior. Then prove commuting laws where the operations are semantically independent.

This can expose hidden algebraic simplifications in the outer learner composition.

### EAT-27: finite confluence / path equivalence

When two legal micro-steps act on disjoint state components, prove that their two execution orders produce definitionally equal or propositionally equal finite states. This gives a local confluence theorem for the coupled pipeline without invoking rewrite-system termination theory over an infinite object.

### EAT-28: exact terminal-optimality certificate

Replace vague optimization language with a finite certificate: after a bounded search/emission pass, the selected archive incumbent is at least as good as every explicitly enumerated candidate in the finite candidate set.

This is an algebraic finite optimum theorem. It does not claim global optimum over an infinite parameter space.

### EAT-29: finite OpenES-to-archive conservation law

Compose the antithetic estimator, mean update, candidate evaluation, and finite archive insertion into one theorem showing exactly which quantities are preserved/cancelled across the complete outer step.

The important distinction is that this is a finite identity/invariant theorem, not an OpenES convergence theorem.

## What is not yet justified by the present abstractions

A numeric Jacobian norm bound cannot be derived merely from an abstract representation certificate. A local contraction theorem likewise requires an explicit finite discrepancy measure and a contraction/bound certificate. The catalog therefore marks those theorems as requiring new certificates instead of pretending that `refl` proves them.

Likewise, finite exact-Rational oracle agreement does not justify global stochastic convergence. It is an independent finite cross-check only.

## Oracle policy

The kernel is the authority. Other language CI can be retained only as independent evidence generators:

- finite reference-value cross-checks;
- independent implementation checks;
- syntax/build regression checks for generated artifacts;
- deterministic example enumeration;
- comparison of exact theorem witnesses.

Other language CI must not certify Agda theorems, rewrite theorem statements, inject hidden axioms, or introduce obsolete algorithms into the active semantics.

The current `ci/agda-v147-kernel-live` branch contains four active workflow files, all Agda-oriented: `agda-kernel-live.yml`, `agda-modular.yml`, `agda-proof-dag.yml`, and `agda.yml`. The v150 branch now also runs two independent exact-Rational oracle implementations in parallel and requires their canonical outputs to agree before the oracle job is green.

The recommended retirement rule for historical FP CI is semantic, not linguistic: delete a workflow when it encodes a superseded algorithm, a stale theorem contract, or a second definition of the semantics. Keep an independent FP checker only when it still computes a useful finite cross-check that is intentionally independent of the Agda implementation.

## Replication record

Each theorem should be tracked with:

`theorem_id, stage, statement_shape, assumptions, finite_or_infinite, proof_status, kernel_status, external_oracle_status, semantic_version, source_path, notes`

A theorem marked `kernel-proved` must correspond to a fresh `agda --safe` check of the relevant stage or root. External agreement alone never changes `proof_status`.
