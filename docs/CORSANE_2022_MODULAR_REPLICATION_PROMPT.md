# Corsane-2022-style modular replication contract

This page is the repository-local replication prompt for the current formalization. It preserves the project's existing **Corsane-2022-style** convention: a wiki-readable experiment contract paired with a flat CSV layout. It is a formatting and replication contract, not a claim that every column originates verbatim from a single source paper.

## 1. Objective

Replicate the finite algebraic learner and representation semantics while keeping three evidence layers separate:

1. **Kernel evidence:** Agda 2.8.0 with `--safe`.
2. **Oracle evidence:** independent exact-rational Haskell, Elixir, Ruby, and SymPy checks.
3. **Empirical evidence:** raw task-level returns and phenotype metadata in CSV; never substitute an oracle result for a measured return.

The modular proof DAG is the primary mathematical surface. The monolithic `Exotic/ERL/FullCoupled/CompleteSafe_v147.agda` is retained as a compatibility/regression target until its legacy scope surface is fully normalized.

## 2. Current architecture

There is one LSTM representation layer. For each representation layer the intended composition is:

`Affine -> LayerNorm(L1 or L2) -> coupled L2 regularization`,

with the LSTM's internal `tanh` and `sigmoid` gates retained as genuine recurrent nonlinearities. The previously redundant standalone representation `tanh` boundary is not part of the canonical representation interface.

The critic-side algebra remains finite and symbolic. No floating point is admitted into the proof layer.

## 3. Algebraic boundary

The finite scalar interface is organized around:

- `Ring` for addition, multiplication, negation, and their laws;
- `OrderedRing` for finite order reasoning and positivity;
- `SmoothAlgebra` for abstract `exp`, `log`, `tanh`, `sigmoid`, square root, reciprocal, and max/min operations;
- explicit square-root domain witnesses;
- explicit nonzero/positive reciprocal laws;
- finite vectors and matrices built from the scalar carrier.

The intended root contract is domain-carrying rather than analytic:

`sqrtDomain x -> sqrt(x) * sqrt(x) = x`.

The intended reciprocal contract is likewise conditional:

`d != 0 -> d * recip(d) = 1`.

This is sufficient for a constructive finite-algebra proof when the surrounding theorem supplies the required domain witness. Full real completeness, limits, measurability, integrals, and stochastic asymptotics are deliberately outside this proof boundary.

## 4. LayerNorm variants

### L2 canonical

The L2 branch may use a variance-like denominator, square root, and reciprocal. The proof obligation is therefore primarily a denominator-domain obligation plus the corresponding algebraic normalization identities.

### L1 ablation

The L1 branch is treated as a separate algebraic primitive family. Its forward normalization can be expressed using absolute values and a strictly positive denominator convention. The non-smooth point at zero is not a reason to abandon the finite proof strategy; it changes the AD contract.

For an exact classical VJP, the L1 branch must either:

- restrict the derivative law to a nonzero/sign-stable domain, or
- state an explicit zero/subgradient convention as part of the primitive.

No theorem in this repository should silently pretend that `abs` has a unique classical derivative at zero.

## 5. Why the present Agda failures are not a real-analysis barrier

The observed v149 failures have been source-boundary failures rather than analytic theorem failures.

Examples already observed in CI include:

- `OrderedRing.base` being referenced although the active record exposes `OrderedRing.ring`;
- duplicate `SmoothAlgebra` surfaces;
- duplicate `matVec` declarations;
- malformed higher-order congruence/parser boundaries in generated theorem blocks.

These errors occur before the relevant theorem obligations are even type-checked. Independent modular `--safe` surfaces have continued to pass while the monolithic integration target has failed earlier in its parse/scope pipeline.

Accordingly, roots, reciprocals, and transcendentals are not the immediate reason for the repeated failures. They are only a source of additional algebraic contracts once the namespace/declaration surface is coherent.

## 6. Efficient-CHAD status

The project uses Efficient-CHAD first. The current finite source-to-source transliteration provides a kernel-checked structural semantic surface. It should not be described as a wholesale import of the upstream paper's complete optimizer/complexity development unless those additional theorems are independently ported and checked.

The next useful CHAD theorem boundary is sequence composition for the single LSTM layer: primitive gate VJPs composed over the recurrent step and then over a finite trajectory.

## 7. Gallici theorem extraction

Gallici et al., `Simplifying Deep Temporal Difference Learning` (ICLR 2025; arXiv:2407.04811), is relevant as a theorem/design blueprint. Its central result concerns provable stability/convergence of deep TD with LayerNorm-style regularization without relying on target networks, including off-policy training.

What is directly extractable into this repository is the **algebraic skeleton**:

- normalization identities and explicit denominator-domain conditions;
- bounded activation contracts for `tanh` and `sigmoid`;
- explicit coupled L2 regularization equations;
- finite one-step TD identities;
- finite Jacobian/VJP bounds as certificates.

What is **not** automatically transferred is the full paper-level convergence theorem. A complete transfer would require the paper's analytic stability framework, stochastic assumptions, and other non-finite reasoning that the current `--safe` project intentionally does not formalize.

## 8. Theorems currently supported by the project direction

1. Finite ring/vector/matrix identities.
2. Structural Efficient-CHAD primal-preservation identities on the supported finite syntax.
3. First-class recurrent LSTM primitive/VJP identities.
4. Finite q-projection and terminal uniqueness identities where their explicit domain hypotheses are supplied.
5. Domain-carrying LayerNorm closure identities for the supported normalization surface.
6. Independent exact-rational oracle agreement for the functional learner traces.

These are kernel/oracle claims only; they do not constitute a global stochastic convergence theorem for the complete RL system.

## 9. Conjectures / next formal targets

### Conjecture A — finite coupled TD stability

For the one-layer composition `Affine + LayerNorm + coupled L2 + LSTM(tanh,sigmoid)`, a bounded finite-horizon Jacobian/VJP certificate should imply a corresponding algebraic one-step TD stability inequality under an explicit step-size/domain contract.

### Conjecture B — L1 LayerNorm VJP closure

A domain-indexed L1 LayerNorm VJP should close constructively when the normalization denominator is nonzero and a sign-stability or explicit zero convention is carried in the theorem state.

### Conjecture C — modular/monolithic equivalence

After the remaining namespace and duplicated-declaration repairs are eliminated, the monolithic `CompleteSafe_v147` target should be reducible to the same theorem surface already passing in the modular DAG.

### Conjecture D — finite Gallici-style extraction

The algebraic identities used around LayerNorm and L2 regularization can be packaged into a finite stability lemma that is useful without claiming the full asymptotic theorem from the paper.

## 10. Missing items

The next missing items are ordered by dependency rather than by conceptual difficulty:

1. Finish the monolithic declaration/scope normalization and obtain a fresh `CompleteSafe_v147` `--safe` pass.
2. Persist the kernel-checked source and remove temporary source-mutating repair machinery from the authoritative workflow.
3. Re-run the now non-mutating Agda gate from a clean checkout.
4. Add the finite one-step coupled-L2/Jacobian stability lemma.
5. Add the L1 LayerNorm primitive/VJP contract, explicitly handling the zero kink.
6. Compose the recurrent LSTM VJP theorem over a finite trajectory.
7. Extend the exact-rational oracle schema only where semantics are already kernel-specified.
8. Replicate missing external environments only when their exact runtimes are available; otherwise record `NA` rather than a proxy score.

## 11. Replication rules

Use fresh seeds for fresh experiments. Preserve full-precision genotype/state during the run. Do not inject historical fitness into a fresh archive. Do not round measured task returns. A post-hoc rounded representation may be reported only after fresh winner selection and must never replace the raw return.

Keep per-task returns separate from proof status. A successful oracle or `--safe` proof is not itself a benchmark score.

The project already keeps security-oriented GitHub Actions as a separate engineering layer. Those checks should remain orthogonal to the mathematical gate rather than being used as substitutes for it.

## 12. Flat CSV layout

The companion layout is `docs/MODULAR_REPLICATION_LAYOUT.csv`. Each row should preserve provenance and distinguish candidate metadata, proof state, oracle state, and empirical task results.

Recommended current columns:

`candidate_id,stage,parent_candidate_id,method,archive_family,emitter,representation,layernorm_norm,critic,trace_rule,q_projection,l2_coupling,munchausen,fitness_definition,seed_group,seed_count,horizon,task,task_return,td_objective,archive_coordinate_1,archive_coordinate_2,archive_incumbent,operator_contract,proof_stage,proof_status,oracle_status,provenance,notes`

For multi-task archives, use one row per candidate-task observation or a deterministic wide schema; do not mix the two conventions in the same dataset.

## 13. Wiki/page layout

### Status

`Agda --safe`: report the exact current gate result and failing declaration when not green.

### Algebra

List the active `Ring`, `OrderedRing`, `SmoothAlgebra`, normalization, and regularization contracts.

### Proofs

List only theorems actually kernel-checked. Separate finite identities from conjectural convergence claims.

### Oracles

Record exact-rational cross-check implementations and their status independently.

### Findings

Record fresh measured returns and formal findings without conflating them.

### Conjectures

List the next finite theorem with all required domain hypotheses.

### Missing replication

Mark unavailable external environments as `NA`; specify the exact runtime and seed requirements for a future replay.

### Next

The immediate dependency chain is: monolith scope closure -> persist source -> clean non-mutating gate -> finite coupled stability -> L1 VJP -> trajectory-level recurrent VJP -> benchmark replication.

## 14. Research references

Matteo Gallici, Mattie Fellows, Benjamin J. Ellis, Bartomeu Pou, Ivan Masmitjà Rusiñol, Jakob Foerster, and Mario Martín. `Simplifying Deep Temporal Difference Learning`. ICLR 2025 / arXiv:2407.04811.

Shuang Wu, Guoqi Li, Lei Deng, et al. `L1-Norm Batch Normalization for Efficient Training of Deep Neural Networks`. IEEE TNNLS (2019). This motivates treating L1 normalization as a viable algebraic ablation while making its zero/sign derivative convention explicit.

## 15. Acceptance criterion for the next merge

Do not land the v149 PR merely because the repair scripts succeed. The required evidence is a fresh clean-checkout `--safe` pass of the complete target plus the independent exact-rational oracle pass. Once those are green, use the repository's configured squash path; normal merge and rebase are disabled in the repository settings.