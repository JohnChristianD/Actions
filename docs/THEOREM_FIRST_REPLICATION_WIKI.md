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

Every learnable parameter block gets its own F4 state: embedding, attention Q/K/V/O, GRU update/reset/candidate, output projection, DPG actor, DPG critic, and Noisy-Net `mu3` and `sigma3`. Frozen RoPE, sparsemax, frozen Haar, and fixed tokenizer structure are not promoted to parameter-bearing blocks.

## Global coupling

The optimizer and L2 controls are global coordinates of the recurrent learner, not method-local optimizer fragments. `GlobalOptimizer.agda` and `GlobalL2.agda` both witness their tokens and prove recurrent-step preservation. The endogenous composition carries these global invariants together with the GRU, DPG actor/critic, and Watkins trace state. fileciteturn127file0 fileciteturn128file0

The DPG actor is deterministic, but the canonical Bellman/max-Q bridge is conditioned on the explicit `IsGreedy` premise. The repository does not silently identify an arbitrary deterministic actor with a greedy policy.

Watkins is the trace mechanism. The canonical theorem surface includes finite trace cutting and the exact one-step regime induced by a cut. It is not SARSA by naming drift, and three recurrent GRU matrices do not imply a TD(lambda) value of lambda.

## Endogenous theorem composition

The canonical composition packages the learner boundaries rather than presenting isolated component facts:

`F4 residual reconstruction -> parameter-bank uniformity -> frozen operator family -> GRU/optimizer invariants -> front-end factorization -> global L2/optimizer preservation -> Watkins trace cut -> greedy DPG/max-Q bridge`.

The finite operator-family skeleton includes sparsemax, frozen Haar, dyadic RoPE, and the finite Mobius/GRU composition layer. Embedding removal is formalized as preserving that operator-class family; embedding remains a distinct learnable parameter block.

The finite Mobius modules prove associative function composition and identity laws. They do not claim a completed coefficient-level `PSL(2,R)` formalization. Likewise, the current Haar object is a finite integer Hadamard/Haar-like operator, not an Agda proof object for the full continuous group `O(2^n)`.

## Noisy Nets comparison status

Flat-dyadic Noisy Nets are stronger than the MR15-GA and OpenES comparison ablations in theorem-class breadth when judged on the endogenous learner surface, because the Noisy-Net construction participates inside the coupled learner and can compose with the global optimizer/L2 invariants, recurrent GRU algebra, sparsemax/representation layer, DPG actor/critic, Watkins trace carrier, and Mobius associative scan structure.

That is a theorem-surface comparison, not an empirical-performance claim. MR15 and OpenES remain useful finite exploration ablations, but they are not the canonical learner semantics. Their historical optimizer/replication variants are pruned from the active contract.

## Replication contract

Replication means reproducing the current canonical definitions and then checking them with `agda --safe`. Generated theorem candidates are only candidate text until the Agda kernel accepts concrete proof terms. Discovery tooling cannot upgrade a conjecture into a theorem.

The active theorem graph should remain connected to the canonical endogenous aggregate. A lemma or source fragment is disconnected when it has no role in the canonical imports, canonical aggregate, or an explicitly retained comparison-ablation gate. Such disconnected historical variants should be deleted from the active branch instead of being preserved as parallel semantics.

The CI policy therefore treats the current endogenous surface as the replacement target for superseded replication prompts. It does not preserve old v147/v149 optimizer recipes, retired optimizer families, or alternate semantics merely as compatibility promises.

## Precision boundary

Keep the imported recurrent/action libraries Int8. Add a dedicated dyadic-rational library only where literal Int8 storage cannot express an exact residual needed by the F4 algebra. Do not introduce a general real-number analysis layer merely to state the finite optimizer. The canonical proof target remains finite/dyadic and `--safe`.

## Convergence and optimization laws

Lyapunov descent, fixed-point uniqueness, cycle exclusion, Banach contraction, and KKT conditions are not impossible over dyadic or Int8 state spaces. They are additional theorem packages that require additional structure.

For a finite deterministic state transition, eventual periodicity is guaranteed by finiteness, so convergence to a fixed point is not automatic. A strict well-founded ranking, a finite Lyapunov function that decreases off fixed points, or an explicit cycle-exclusion theorem can prove fixed-point convergence. A finite metric space is complete, so a genuine contraction mapping can support a Banach-style fixed-point theorem, but the contraction metric and contraction inequality must actually be formalized; modular Int8 arithmetic does not provide them for free.

KKT requires an explicitly defined optimization problem, constraints, an order/inequality structure, and a stationarity notion. Literal modular Int8 arithmetic is not a substitute for those objects. A dyadic ordered carrier can support a discrete KKT-like theory when the objective, feasible set, and necessary optimality conditions are encoded explicitly.

None of these stronger convergence/optimality results is claimed merely from the present global optimizer and global L2 preservation laws. Those current laws establish shared control persistence, not descent or uniqueness.

## Canonical theorem surface

The active connected surface is:

`F4-Int-U-Softsign + global optimizer + global L2 + norm-pair boundary + finite Mobius composition + associative scan/GRU composition + Noisy Nets + sparsemax/Haar/RoPE front end + Watkins trace carrier + DPG actor/critic + greedy max-Q bridge + finite representation/CHAD support`.

The comparison-only surfaces are the finite MR15 and OpenES exploration variants. They remain ablation gates when explicitly checked, but they do not define the learner.
