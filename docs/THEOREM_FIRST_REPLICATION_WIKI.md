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

The finite Mobius modules prove associative function composition and identity laws. They do not claim a completed coefficient-level `PSL(2,R)` formalization. Likewise, the current Haar object is a finite integer Hadamard/Haar-like operator, not an Agda proof object for the full continuous group `O(2^n)`.

## Sparsemax canonical versus stronger optional class

The canonical Sparsemax remains fixed because that surface already has exact finite hard-sparsity and boundary-idempotence theorems. This is the cleaner closed theorem surface.

A strictly richer optional endogenous parameterization now exists in `Exotic/ERL/FullCoupled/SparsemaxF4Composition.agda`. It gives Sparsemax its own F4-learned bias/temperature state and a further variant with separate Noisy-Net-style `mu`/`sigma` F4 states. This enlarges the coupled parameter graph, but its concrete application must independently prove finite closure, hard-sparsity, and idempotence. Those properties do not follow automatically once Sparsemax itself is perturbed.

Thus the intended hierarchy is:

`fixed Sparsemax` = canonical closed theorem surface;

`F4-learned Sparsemax` = stronger learnable theorem class/ablation;

`F4-learned + Noisy-Net Sparsemax` = strongest parameter-coupled exploration variant once its finite closure theorems are concrete.

This is a theorem-breadth distinction, not an empirical-performance ranking.

## Flat-dyadic exploration comparison status

Flat-dyadic law remains the common finite exploration law across the three comparison mechanisms:

1. MR15: `Exotic/ERL/Exploration/MR15Reachability.agda`
2. OpenES: `Exotic/ERL/Exploration/OpenESDyadic.agda`
3. Noisy Nets: `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

Flat-dyadic Noisy Nets are the broadest theorem-class surface among the three when judged by endogenous coupling, because the noise state participates inside the learner and can compose with recurrent GRU algebra, global optimizer/L2 control, representation, Watkins traces, DPG actor/critic, Sparsemax/Haar/RoPE, and Mobius associative composition. MR15 and OpenES remain comparison ablations rather than alternate canonical learner semantics.

This is a theorem-surface comparison, not a claim that Noisy Nets empirically outperform MR15 or OpenES.

## Associative scan and window semantics

`Exotic/efficient_chad/ParallelPrefix.agda` proves that any binary reduction of the same finite transition sequence agrees with its serial composition, using associative transition composition. This supports arbitrary finite window lengths in the inductive `List` representation.

This is not a theorem about an actually infinite sequence or an infinite cardinality window. “Unbounded window” here means no fixed finite window length is hard-coded into the algebra: every finite list length is handled by the same associative scan law.

## Precision and imported dyadic carrier boundary

Keep the imported recurrent/action libraries Int8. The imported dyadic carrier does **not** mean the learner is secretly using unbounded dyadic precision.

It exists because literal signed Int8 cannot represent exact residuals such as `1/2`. The additional carrier therefore supplies only the finite-precision dyadic representation and the operations required by the exact finite proofs. Depending on the operator, those operations can include exact fractional residual addition/subtraction, bounded scaling, quantization, rounding, or finite-domain division/reciprocal/normalization.

The finite Haar theorem demonstrates the same boundary explicitly: exact `1/sqrt(2)` normalization is not imported because it is non-dyadic. The finite Sparsemax implementation can still use integer division on its 255-grid formula.

A dedicated dyadic-rational library should be added only when such an operation cannot be represented cleanly in the existing Int8-facing libraries. It is not a license to introduce unrestricted real analysis.

## Quantization and convergence claims

A statement such as “the optimizer converges with minimal quantization effect to the closest quantized fixed point to the L2-biased Bellman optimum” is a strong target theorem, not an automatic consequence of F4 residual reconstruction.

To promote that statement to a kernel theorem, the repository must provide an explicit Bellman or regularized fixed-point operator, an explicit L2-biased fixed point, a concrete quantizer and finite metric/order, a nearest-quantized-fixed-point law, and a Lyapunov or contraction argument excluding nontrivial cycles. The present global optimizer/L2 preservation theorems do not by themselves establish those facts.

Recent SciSpace results are consistent with this separation: low-precision adaptive-optimizer convergence can be proved under explicit quantization-error assumptions, while sparse policy parameterizations can carry their own convergence structure. Those results motivate the theorem shapes but do not transfer automatically to this F4/Int8/Watkins/DPG system.

## Stability theorem frontier

`Exotic/ERL/FullCoupled/Int8StabilityComposition.agda` is now part of the `--safe` workflow. It contains:

- a constructive theorem that a strict Nat-valued Lyapunov law excludes nontrivial 2-cycles;
- a finite metric/contraction certificate surface for Banach-style reasoning;
- a discrete KKT certificate surface with explicit primal, dual, stationarity, and complementarity components;
- an explicit quantized-fixed-point certificate surface.

These are deliberately hypothesis-driven. The CI gate will reject any attempt to turn them into stronger global convergence claims without concrete witnesses.

## KKT, Banach, fixed points, and cycles in Int8

None is intrinsically impossible in dyadic or Int8 state spaces. What is unavailable for free is the required extra structure.

A strict well-founded Lyapunov ranking can exclude cycles and establish convergence when combined with an appropriate reachability argument. A finite metric is complete, so a genuine contraction theorem can support a Banach-style fixed-point result. KKT requires an explicitly defined discrete/dyadic optimization problem and its necessary optimality conditions. Bare modular Int8 arithmetic is not itself a Lyapunov function, metric contraction, or KKT system.

For finite deterministic state spaces, eventual periodicity is the default consequence of finiteness. Therefore the canonical route to genuine fixed-point convergence is a concrete cycle-exclusion or contraction/descent theorem, not an assumption that finite precision removes cycles.

## Replication contract

Replication means reproducing the current canonical definitions and checking them with `agda --safe`. Generated theorem candidates are only candidate text until the Agda kernel accepts concrete proof terms. Discovery tooling cannot upgrade a conjecture into a theorem.

The active theorem graph remains connected to the endogenous aggregate. Disconnected historical lemmas, superseded v147/v149 recipes, and retired optimizer variants are pruned rather than maintained as parallel semantics.

The active connected theorem surface is:

`F4-Int-U-Softsign + global optimizer + global L2 + norm-pair boundary + finite Mobius composition + associative scan/GRU composition + Noisy Nets + sparsemax/Haar/RoPE front end + Watkins trace carrier + DPG actor/critic + greedy max-Q bridge + finite representation/CHAD support`.

The comparison-only surfaces are the finite MR15 and OpenES exploration variants. They remain ablation gates when explicitly checked, but they do not define the learner.
