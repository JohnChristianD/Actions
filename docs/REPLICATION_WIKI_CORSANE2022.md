# Replication Wiki — Corsane-Style 2022 Layout

Status: active formal-replication record
Scope: algebraic Agda closure, functional cross-checks, and theorem-boundary diagnosis
Primary gate: `agda --safe Exotic/ERL/FullCoupled/CompleteSafe_v147.agda`

## Abstract

The present closure effort is not blocked by a demonstrated need for full real analysis. The current failures expose ordinary Agda grammar and source-structure defects first. A fresh CI run reached a `where` placement parse failure in `LayerNorm`; after a targeted scope repair, the next gate reached a malformed dependent `with` lambda in the pullback accumulator. These are syntax-boundary failures, not evidence that roots, logarithms, exponentials, Gaussian mutations, or LSTM composition inherently force a real-analytic formalization.

The replication architecture therefore keeps the algebraic core total where possible and carries domain conditions as explicit typed witnesses. Partial analytic behavior is represented by abstract operations plus only the laws needed by a given theorem. This keeps `--safe` closure honest: no proof is obtained by replacing an unresolved law with an unchecked postulate or by hiding a parser/type problem behind a CAS oracle.

## Reproduction Contract

1. Start from the repository's current main-line algebraic source.
2. Canonicalize duplicate declarations before theorem repair.
3. Keep every repair deterministic and idempotent.
4. Run Agda `--safe` after each structural repair layer.
5. Promote source changes only from a repair branch.
6. Use pull requests and the repository's configured squash-merge path when the complete gate is green.
7. Keep auxiliary exact-rational checks functional and independent of SymPy.
8. Preserve the existing Astro and Rails Actions; the replication gate is additive.
9. Treat a parser failure, scope failure, type failure, missing equality, and genuinely missing mathematical law as different classes of defect.

## Current Findings

### Finding A — duplicate algebraic surface

The monolith accumulated a second `SmoothAlgebra` and repeated vector/matrix operations. The duplicate surface also introduced a field-name mismatch: parts of the second block use `OrderedRing.base`, while the canonical ordered-ring record uses `ring`. Deduplication must therefore precede theorem closure.

### Finding B — LayerNorm was a grammar failure

The `LayerNorm` record placed a `where` block immediately after its field list. The target helper was only an alias of `epsilon`, so the clean algebraic repair is to keep the domain witness as a record field and remove the local `where` declaration.

### Finding C — pullback accumulation was a grammar failure

The form `state (lambda j with finDecEq ...)` is not a valid Agda term in this location. The repair lifts the dependent branch into a named `accumulateAt` helper and then passes that helper as an ordinary function.

### Finding D — exact symbolic oracle removed

The repository previously contained a SymPy-based exact-rational certificate and a workflow step installing/running it. The repair branch removes that oracle and replaces the cross-check with Haskell exact-rational traces, Elixir exact-rational traces, and a Ruby `Rational` certificate. Agda remains the proof authority.

## Algebraic Core

Let `R` be a carrier equipped with the algebraic operations actually needed by the theorem layer. Let finite vectors be indexed by `Fin n` and matrices by nested finite indices.

For a layer state `x`, weight map `W`, bias `b`, and activation `act`, use the compositional form

`x' = act (W x + b)`

and make every normalization and regularization operation explicit in the term graph.

For L1 weight normalization, parameterize each row by

`w = (g / ||v||_1) v`

with an explicit nonzero witness for `||v||_1` wherever division is represented as a partial algebraic operation. The 1-path quantity is represented recursively by absolute-weight composition; at the matrix level the basic MLP form is

`P1(W) = 1^T |W_K| |W_(K-1)| ... |W_1| 1`.

This is exactly the useful bridge from parameter-space structure to a path-composition invariant. The cited paper establishes the corresponding path expression and a Lipschitz upper-bound theorem under globally bounded activation subgradients. It also shows that shared L1-normalization gains simplify the path quantity for MLPs.

For coupled layerwise L2 decay, use an algebraic potential such as

`L2(theta) = sum_l lambda_l * ||W_l||_2^2`

or a coupled variant over the complete parameter block. Do not silently identify this quantity with the 1-path quantity: they control different algebraic aspects and introduce different scale symmetries.

For LayerNorm, carry a denominator-domain witness explicitly. A square-root layer may be represented by an abstract operation `sqrt` together with a domain predicate and a square law on that domain. No global real square-root theorem is needed merely to type the layer.

For sign activation, define a total sign-valued operation and a separate stable-region relation. Classical differentiability is then invoked only under a sign-stability hypothesis. This separation is essential: literal sign activation has a boundary at zero, so a global classical Jacobian theorem is not available without changing the activation semantics.

## Theorem Inventory

### Proven structural goals

Canonical declaration uniqueness can be checked syntactically.

The pullback accumulator can be represented as a total finite function once its dependent case split is lifted into a named helper.

LayerNorm can carry its denominator domain as a typed witness.

Exact-rational algebraic identities can be cross-checked with pure functional implementations without a symbolic CAS dependency.

### Paper-backed theorem input

The 1-path norm of an MLP is a sum of absolute products over input-output paths, with the matrix expression above. Under globally bounded activation subgradients in the stated norm pairing, the cited paper reports the standard path-norm Lipschitz bound. For its CReLU residual construction, it reports a tighter path subset bound.

These results are useful as imported theorem statements or as targets for a separate Agda formalization, but they do not directly prove the combined sign-activation + LayerNorm + coupled-L2 architecture.

## Conjectures

### Conjecture 1 — normalized path/L2 compatibility

On a finite normalized parameter quotient, a combined objective

`J(theta) = alpha * P1(theta) + beta * L2(theta)`

should give simultaneous control of path growth and layerwise quadratic parameter size, provided the L1 normalization denominator and all LayerNorm denominators remain inside explicit domains.

The quotient qualification matters because weight normalization creates scale redundancy. A direct coercivity statement on raw parameters can fail even when the represented network is stable.

### Conjecture 2 — stable sign-region sensitivity

On a region in which every sign preactivation remains nonzero and every LayerNorm denominator remains in its domain, the composed network admits an algebraic sensitivity certificate obtained by composing the layer maps and the local sign/normalization laws. The theorem should be stated conditionally on these stability witnesses rather than pretending sign is globally smooth.

### Conjecture 3 — Gaussian mutation abstraction

An OpenES-style Gaussian mutation layer can be separated from the deterministic algebraic network semantics. The deterministic network proof needs only the mutation operator's typed input/output contract unless a theorem explicitly claims a probability law, concentration result, or expectation identity. Those distributional claims belong to a separate probability layer.

## Why Closure Kept Failing

The evidence points to a layered failure order.

First: parser and declaration-scope defects.

Second: duplicated records, namespace collisions, and field-name mismatches.

Third: dependent pattern and finite-index typing obligations.

Fourth: algebraic equality proofs and missing domain witnesses.

Only after those gates clear can a genuinely analytic dependency be identified. A failed proof at an exponential, logarithm, reciprocal, square root, or Gaussian-law boundary must not be labeled a real-analysis impossibility without first seeing the exact Agda typing obligation.

## Roots, Transcendentals, LSTM, LayerNorm, OpenES

Roots and reciprocals are not intrinsically a blocker to algebraic Agda. The safe pattern is a total carrier together with explicit domain predicates and laws. This is enough whenever the theorem only needs an identity such as `sqrt(x) * sqrt(x) = x` under a domain witness.

Exponentials, logarithms, and tanh are different only when the theorem asks for analytic facts rather than symbolic composition. A formal layer can expose `exp`, `log`, or `tanh` as typed operations. Their derivative laws, monotonicity, inverse laws, or analytic expansion require additional structure exactly when a theorem uses those facts.

LSTM adds sigmoid and tanh gates plus recurrent state. The recurrent state algebra itself is finite and compositional. The analytic burden appears only in claims about derivatives, global smoothness, or quantitative sensitivity of those nonlinearities.

LayerNorm introduces reciprocal and square-root domains. Those are local algebraic side conditions until a theorem asks for global bounds over a full real domain.

OpenES introduces a mutation mechanism whose Gaussian distribution is a probabilistic object. A deterministic algebraic theorem can abstract over the mutation operator. A theorem claiming exact Gaussian probability identities needs a probability formalization; this is not a reason to weaken the deterministic kernel theorem.

## Relation to the L1 Weight-Norm + 1-Path-Norm Paper

The paper is relevant as a design analogue and theorem source, not as a plug-in proof.

The strongest transferable piece is the MLP path algebra: L1 weight normalization gives a natural normalized parameterization, while 1-path norm composes multiplicatively across layers. The paper explicitly presents the MLP path formula and connects the path quantity to a Lipschitz bound under activation-subgradient assumptions.

The gap is equally important. The paper's theorem is built around activations with bounded subgradients and its residual construction uses CReLU. Literal sign activation is discontinuous at zero, LayerNorm introduces denominator domains and gain/shift structure, and coupled-L2 decay creates an additional regularizer. Therefore the combined theorem must be new.

A sensible Agda decomposition is:

`L1Normalize -> Affine -> SignStable -> LayerNormDomain -> CoupledL2 -> Composition -> SensitivityCertificate`

with each arrow represented by an explicit typed interface and theorem. The path quantity should be a separate invariant that can be connected to the composed sensitivity certificate only under the hypotheses that actually make that connection valid.

## Missing Pieces

The remaining blockers are source normalization and kernel closure, followed by the first non-syntactic obligation exposed by the kernel. The exact next theorem is intentionally not guessed: it should be taken from the first post-parser Agda error after the current structural repair passes.

Further missing formal content likely includes a canonical finite-index formulation of L1 normalization, explicit sign-stability predicates, LayerNorm denominator lemmas, compatibility lemmas between path composition and normalization gains, and a separate probabilistic interface for OpenES mutation laws.

A full real-analytic development should be added only if a later theorem genuinely requires derivatives, continuity on infinite domains, asymptotic approximation, or a probability theorem that cannot be factored through a finite algebraic interface.

## Replication Sequence

Stage 1: canonicalize declarations and names.

Stage 2: eliminate malformed dependent-expression syntax.

Stage 3: kernel-check all finite vector, matrix, normalization, and recurrence interfaces.

Stage 4: close algebraic equalities and explicit domain witnesses.

Stage 5: formalize stable-region sign semantics.

Stage 6: connect L1 normalization to the 1-path recurrence.

Stage 7: add coupled-L2 decay as an independent algebraic potential and prove only the interaction laws needed by the target theorem.

Stage 8: add abstract LSTM nonlinearities and only the derivative laws required by the CHAD layer.

Stage 9: keep OpenES mutation as an effect-explicit interface; add probability laws only in a separate probability module.

Stage 10: run the full `--safe` gate and then open a normal pull request using the repository's squash-merge configuration.

## Acceptance Criteria

A replication is complete only when the monolith passes Agda `--safe`, no unchecked postulate substitutes for a failed theorem, duplicate canonical declarations are absent, the exact-rational functional cross-checks pass, and the theorem catalog distinguishes proved statements from conjectures.

## Source References

Aditya Biswas, “Hidden Synergy: L1 Weight Normalization and 1-Path-Norm Regularization”, arXiv:2404.19112v1 (2024). Section 2 defines L1 weight normalization; Section 3 gives the MLP 1-path expression and the stated Lipschitz bound; the CReLU residual result appears as Theorem 2.

The requested “Corsane 2022” source was not identified with enough confidence to attribute a specific citation. This page therefore uses “Corsane-Style 2022 Layout” as a layout label only, not as a bibliographic claim.

## Current Next Action

Continue from the exact first Agda kernel error after the accumulate-helper repair. Do not jump to real analysis. Do not reintroduce SymPy. Do not alter the activation, normalization, regularization, or mutation semantics merely to make the parser pass.
