# Canonical theorem-first replication wiki

Authority: Agda `--safe`.

The canonical learner is the finite/dyadic endogenous composition rooted at `Exotic/ERL/FullCoupled/EndogenousBoundaryComposition.agda`. `AllSafeCombined.agda` remains the regression bundle, while this document describes the actual learner semantics. Retired optimizer families, superseded replication recipes, and historically incompatible variants are not canonical inputs and must not be reintroduced merely because they existed in older commits.

## Canonical learner

The learner is finite and low-precision at the imported model boundary. Existing Int8 libraries remain the storage and recurrent/action surface. The F4 optimizer uses a dyadic scalar carrier only where exact residual arithmetic requires values such as one-half that literal signed Int8 cannot represent exactly. This is an implementation-level representation choice, not an expansion to unrestricted real analysis.

Per-parameter F4-Int-U-Softsign state is:

`(theta_q, r_theta, e_q, r_e, r_l, ell)`

with the exact three-level update:

1. momentum reconstruction: `e_full`, then quantize `e_q` and store `r_e = e_full - e_q`;
2. logarithmic step integration: accumulate `r_l + e_full`, round to `Delta ell`, update `ell`, and retain the exact dyadic residual;
3. parameter update: use `2^ell * softsign(g)` together with the parameter momentum term, then quantize `theta_q` and retain `r_theta`.

The dead-zone term is permanently absent from this canonical rule. The defining exact laws are the reconstruction identities for `theta`, momentum, and the log integrator. They are algebraic equalities, not floating-point approximations.

Every learnable parameter block gets its own F4 state: embedding, attention Q/K/V/O, GRU update/reset/candidate, output projection, DPG actor, DPG critic, and Noisy-Net `mu3` and `sigma3`. Frozen RoPE, sparsemax, frozen Haar, and fixed tokenizer structure are not promoted to parameter-bearing blocks in the canonical closed surface.

## Global coupling

The optimizer and L2 controls are global coordinates of the recurrent learner, not method-local optimizer fragments. `GlobalOptimizer.agda` and `GlobalL2.agda` both witness their tokens and prove recurrent-step preservation. The endogenous composition carries these global invariants together with the GRU, DPG actor/critic, and Watkins trace state.

The DPG actor is deterministic, but the canonical Bellman/max-Q bridge is conditioned on the explicit `IsGreedy` premise. The repository does not silently identify an arbitrary deterministic actor with a greedy policy.

Watkins is the trace mechanism. The canonical theorem surface includes finite trace cutting and the exact one-step regime induced by a cut. It is not SARSA by naming drift, and three recurrent GRU matrices do not imply a TD(lambda) value of lambda.

## Endogenous theorem composition

The canonical composition packages the learner boundaries rather than presenting isolated component facts:

`F4 residual reconstruction -> parameter-bank uniformity -> frozen operator family -> GRU/optimizer invariants -> front-end factorization -> global L2/optimizer preservation -> Watkins trace cut -> greedy DPG/max-Q bridge`.

The finite operator-family skeleton includes sparsemax, frozen Haar, dyadic RoPE, and the finite Mobius/GRU composition layer. Embedding removal is formalized as preserving that operator-class family; embedding remains a distinct learnable parameter block.

## Sparsemax: clean base versus strongest theorem class

Fixed Sparsemax is the **clean deterministic proof base**, not the strongest exploration theorem class. It is clean because the existing finite front-end has already closed hard-sparsity and boundary-idempotence laws for that operator, while a deterministic GRU preserves a simple finite transition semantics. That makes it a stable baseline for proving downstream composition, not an exploration claim.

The strict theorem-surface hierarchy is instead:

`fixed Sparsemax + deterministic GRU`

`< F4-learned Sparsemax + global optimizer/L2 + path-norm/L1`

`< F4-learned + Noisy-Net Sparsemax + global optimizer/L2 + path-norm/L1`

`< F4-learned + Noisy-Net Sparsemax + Efficient CHAD boundary`

`< previous class + finite irreducibility/aperiodicity/invariant-measure layer`.

The final entries are broader theorem **surfaces**, not evidence that every listed theorem has already been instantiated with concrete numerical witnesses.

## Global path-norm + L1 pairing

`Exotic/ERL/FullCoupled/LearnedRegularizationComposition.agda` now gives every learned parameter/nonlinearity block an explicit path-norm certificate and L1-weight certificate, including Sparsemax and Noisy-Net `mu3`/`sigma3`. The global optimizer/L2 state is paired with this bank rather than treating regularization as a local exception.

At present these are certificate interfaces, not completed inequalities such as a proved path-norm bound on every concrete weight tensor. A concrete norm formula and the corresponding arithmetic bound remain the next strengthening point.

## Efficient CHAD, CHAD, and iterative CHAD

The external CHAD literature motivates the highest compositional layer. CHAD is explicitly a structure-preserving source transformation with compositional correctness; Efficient CHAD adds efficient reverse-mode structure and an Agda complexity formalization; iterative CHAD extends the compositional framework to iteration. The repository therefore treats Efficient CHAD as the algebraic composition substrate rather than as an unrelated utility.

`Exotic/efficient_chad/DyadicCHAD.agda` carries explicit source/primal/pullback contracts and a compositional cost law. `Exotic/efficient_chad/ParallelPrefix.agda` supplies the finite associative scan theorem. `Exotic/ERL/FullCoupled/EndogenousCHADComposition.agda` connects these to the endogenous learner and learned Sparsemax boundary.

The strongest honest interpretation is: Efficient CHAD is the best existing **composition algebra** in this repository, but it does not automatically differentiate a concrete learned Int8/dyadic Sparsemax. That concrete operator still has to supply the appropriate primal/pullback certificate.

## Flat-dyadic non-separable exploration composition

The old replication table correctly treats flat-dyadic exploration as a common law compared across MR15, OpenES, and Noisy Nets, and it explicitly warns that coordinate-level reachability does not imply full learner+EA irreducibility. fileciteturn128file0

The intended composition theorem is now joint-state rather than “one theorem per coordinate”: the exploration kernel, learner state, population/selection state, optimizer residual state, and recurrent state are all part of the coupled transition relation. `FiniteMarkovComposition.agda` supplies the exact finite theorem surface for irreducibility, self-loop/period-1 evidence, invariant-measure certificates, and coupled-state composition.

The three exploration methods remain theorem-comparison variants. The current repository does **not** promote one of them to a universal empirical winner.

## Associative scan and window semantics

`Exotic/efficient_chad/ParallelPrefix.agda` proves that any binary reduction of the same finite transition sequence agrees with its serial composition, using associative transition composition. This supports arbitrary finite window lengths in the inductive `List` representation.

This is not a theorem about an actually infinite sequence or an infinite cardinality window. “Unbounded window” here means no fixed finite window length is hard-coded into the algebra: every finite list length is handled by the same associative scan law.

## Precision, division, and imported carrier boundary

The imported dyadic carrier does not mean the learner is secretly using unbounded dyadic precision. It exists because literal signed Int8 cannot represent exact residuals such as `1/2`.

The minimum additional exact division surface is now `Exotic/efficient_chad/FiniteDivision.agda`. It adds only a positive finite denominator and a fractional carrier, with division restricted to a provably positive finite denominator. This is intentionally smaller than importing a general rational/field hierarchy.

The correct division boundary is therefore:

`Int8 storage -> exact finite fraction -> quantization/storage code`.

General division by an arbitrary signed value is deliberately **not** claimed until a nonzero-sign/field-style algebra is supplied. This prevents Softsign or normalization formulas from smuggling in an unproved denominator assumption.

The finite Haar theorem similarly avoids importing the non-dyadic `1/sqrt(2)` normalization. Sparsemax can remain exact on its finite integer grid.

## Exact finite-state irreducibility, aperiodicity, and invariant measure

`Exotic/ERL/FullCoupled/FiniteMarkovComposition.agda` now separates:

- full-state irreducibility as a joint reachability certificate;
- aperiodicity as an explicit self-loop/period-1 certificate attached to the joint kernel;
- invariant-measure existence as an explicit finite mass/invariance witness;
- unique invariant measure as an explicit uniqueness certificate rather than an unsupported assertion.

This is deliberately stricter than saying “the state space is finite.” Finite deterministic systems can cycle, and finite stochastic kernels need an actual stochastic/invariant witness before that theorem is promoted.

Formal finite-state Markov-chain literature independently supports this decomposition into exact transition, Chapman-Kolmogorov/steady-state, and ergodic reasoning. The current Agda layer is intentionally smaller and constructive.

## Finite semidirect-product layer

`Exotic/ERL/FullCoupled/FiniteSemidirectComposition.agda` provides the correct finite crossed/semidirect-product architecture: an operator monoid acts on a state monoid, and the coupled pair gets semidirect multiplication.

This is the precise landing zone for the earlier “crossed product / semidirect product” intuition. It is not a claim that every F4 parameter bank is already a nontrivial group. Inverses and action laws must be instantiated before a genuine group theorem is asserted.

## Theorem-variant comparison automation

`Exotic/ERL/FullCoupled/TheoremVariantComparison.agda` makes the comparison axes explicit: fixed versus learned Sparsemax, noise, CHAD, Markov/ergodic structure, path/L1 regularization, and semidirect coupling. The canonical workflow checks this comparison surface under `agda --safe` alongside the underlying modules.

The correct ranking is by theorem-surface inclusion and declared finite criteria, not by a universal “best model” claim. The old replication table already states the stronger form: compare candidates only after full irreducibility, full self-loop, and exact arithmetic are admitted. fileciteturn128file6

## Quantization and convergence claims

A statement such as “the optimizer converges with minimal quantization effect to the closest quantized fixed point to the L2-biased Bellman optimum” remains a strong target theorem, not an automatic consequence of F4 reconstruction.

To promote it to a kernel theorem, the repository still needs an explicit Bellman or regularized fixed-point operator, an explicit L2-biased fixed point, a concrete quantizer and finite metric/order, a nearest-quantized-fixed-point law, and a Lyapunov or contraction argument excluding nontrivial cycles. The present global optimizer/L2 preservation theorems do not by themselves establish those facts.

## Stability theorem frontier

`Exotic/ERL/FullCoupled/Int8StabilityComposition.agda` is part of the `--safe` workflow. It contains:

- a constructive theorem that a strict Nat-valued Lyapunov law excludes nontrivial 2-cycles;
- a constructive theorem that the same strict-descent law excludes **every positive-length finite cycle** whose orbit states are non-fixed;
- a finite metric/contraction certificate surface for Banach-style reasoning;
- a discrete KKT certificate surface with explicit primal, dual, stationarity, and complementarity components;
- an explicit quantized-fixed-point certificate surface.

The all-cycle theorem is constructive because it uses an explicit finite iterate, transports the non-fixed hypothesis along the deterministic orbit, repeatedly accumulates strict decreases in `Nat`, and closes the cycle to derive `energy s < energy s`, contradicted by `Nat` irreflexivity. No classical choice, probabilistic assumption, or infinity argument is used.

## Deterministic versus stochastic theorem promotion

`Exotic/ERL/FullCoupled/EndogenousLyapunovComposition.agda` packages the Lyapunov result over an explicit `EndogenousF4State` transition. This is the directly promotable **deterministic special case**. It proves cycle-freedom only after an actual deterministic step function and strict Lyapunov certificate are supplied.

Finite state alone does not make Markovian exploration ergodic. Irreducibility, aperiodicity, invariant-measure existence, and ergodicity require an explicit stochastic transition kernel and the corresponding finite certificates. Adding action noise or parameter noise can help construct those hypotheses, but noise is not logically automatic and is not required for the deterministic Lyapunov theorem.

## QSA / Bellman strengthening boundary

The same finite machinery makes stronger QSA-style proofs feasible, but only through an explicit update operator. A quantized Q-table or Bellman state can be placed under the same finite metric/Lyapunov/contraction interfaces. A useful promotable route is:

`finite Q-state -> explicit Bellman/QSA step -> contraction or strict Lyapunov certificate -> unique fixed point / cycle exclusion -> quantized fixed-point comparison`.

The existing greedy DPG/max-Q theorem remains a one-step equivalence under `IsGreedy`; it is not yet a convergence theorem for QSA. A stochastic approximation claim additionally needs explicit transition/noise and step-size assumptions.

## KKT, Banach, fixed points, and cycles in Int8

None is intrinsically impossible in dyadic or Int8 state spaces. What is unavailable for free is the required extra structure.

A strict well-founded Lyapunov ranking can exclude cycles and establish convergence when combined with an appropriate reachability argument. A finite metric is complete, so a genuine contraction theorem can support a Banach-style fixed-point result. KKT requires an explicitly defined discrete/dyadic optimization problem and its necessary optimality conditions. Bare modular Int8 arithmetic is not itself a Lyapunov function, metric contraction, or KKT system.

For finite deterministic state spaces, eventual periodicity is the default consequence of finiteness. Therefore the canonical route to genuine fixed-point convergence is a concrete all-cycle-exclusion or contraction/descent theorem, not an assumption that finite precision removes cycles.
