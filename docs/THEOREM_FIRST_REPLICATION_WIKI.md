# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

Repository CI authority: `.github/workflows/agda.yml`, which checks the canonical source, regression bundle, finite exploration modules, law modules, representation-factor theorem, finite Möbius composition, and the generated law×method theorem surface.

## Permanent finite theorem scope

The repository is finite, dyadic, and Int8-oriented. The CI gate permanently rejects the pruned legacy triangular distribution family and other rejected theorem families before Agda proof checking. No rejected family is selectable through source, documentation, generated candidates, or metadata.

No external theorem family is accepted as a proof shortcut. External literature may inform algebraic design, but only repository-local `--safe` proofs are authoritative.

## Actual exploration methods

The actual exploration-method set is exactly:

1. MR15 — `Exotic/ERL/Exploration/MR15Reachability.agda`
2. OpenES — `Exotic/ERL/Exploration/OpenESDyadic.agda`
3. Noisy Nets — `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

Lazy Walk, Dyadic Ladder, and Flat Dyadic are probability-law modules, not exploration methods.

## Probability-law surface

The remaining exact finite law family is:

- Lazy Walk: stay weight 2/4, ±1 weights 1/4.
- Dyadic Ladder: stay weight 16/32, each signed power-of-two through ±128 has weight 1/32.
- Flat Dyadic: every Int8 code has weight 1/256.

`Exotic/ERL/Exploration/DyadicLaw.agda` exposes all three laws with exact normalization, zero support, and ±1 support. The legacy triangular law is absent from this interface.

## Endogenous theorem frontier

A theorem exists only at the full coupling boundary:

`law + actual method + softsign-gated CHAD composition + reachability + self-loop -> PeriodOne`.

`Exotic/ERL/FullCoupled/FullAlgebraicCoupling.agda` records the exact law normalization/unit-support facts, the forward and pullback composition laws for the `signReLU8 -> softsign8` boundary, the actual transition theorem, and the resulting period-one theorem.

The generator `.ci/discovery/ExplorationTheoremGenerator.hs` now enumerates all nine permutations:

`{MR15, OpenES, NoisyNet} × {LazyWalk, DyadicLadder, FlatDyadic}`.

Haskell only constructs the Agda harness. `agda --safe` accepts or rejects the resulting theorem objects.

## Correct representation boundary

Yes: the canonical exploration theorem should be attached to the softsign-gated representation boundary, not treated as an unrelated outer heuristic state.

The forward algebraic path remains:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

`Exotic/efficient_chad/SoftsignGatedComposition.agda` already proves the generic finite CHAD composition law for `softsign8 ∘ signReLU8`. This is an actual kernel theorem about composition, not an activation-specific Möbius theorem.

## Noisy-Net projection/lift theorem

`Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda` now defines a concrete finite representation state

`SoftsignGatedRepresentation = GateParams × Int8`.

It proves a genuine section/retraction and step-level factorization:

`projectSoftsignGated (liftSoftsignGated r) ≡ r`;

`NoisyNetStep s t -> SoftsignGatedStep (project s) (project t)`;

`SoftsignGatedStep r q -> NoisyNetStep (lift r) (lift q)`.

That is the missing bridge needed before treating Noisy Nets as strictly stronger than a representation-only ablation. The strongest Noisy-Net theorem object is therefore a full coupling theorem plus an explicit transition factor into the softsign-gated representation.

MR15 and OpenES still have concrete finite reachability/self-loop theorem shells, but their production-state projection/lift into this same representation boundary is not yet present. The repository therefore does not pretend to have a cross-method strict proof for them.

## Strict theorem ordering

The ordering is a logical theorem-class order, not a witness-count ranking.

Method axis:

`base full-coupling < representation-factor full-coupling`.

`TheoremStrengthV2.agda` proves the representation-factor implication to the base class and gives a finite singleton-state countermodel showing that a base full-coupling theorem does not imply existence of a nontrivial two-point representation factor. Thus the method strengthening is genuinely strict at the theorem-class level.

The concrete method levels are:

`MR15 = OpenES = base level < Noisy Nets = representation-factor level`.

Law axis:

`LazyWalk < DyadicLadder < FlatDyadic`.

This is the exact finite support-strength axis: Lazy Walk proves only the unit generator; Dyadic Ladder additionally exposes power-of-two support; Flat Dyadic exposes every Int8 code directly. The ordering is algebraic support inclusion, not a statistical score.

The combined product order is componentwise. Hence the unique maximal corner currently connected by proofs is:

`Noisy Nets × Flat Dyadic`.

This is a strict theorem ordering under the proved method-factor and law-support axes; it is not an empirical performance claim.

## Möbius composition boundary

`Exotic/efficient_chad/MobiusInt8Composition.agda` now proves exact composition closure for finite homogeneous-coordinate Möbius matrices over the Int8 algebra:

`M₂ ∘ M₁` is represented by the exact Int8 matrix product, and the induced projective action satisfies the composition equation definitionally.

This is the correct algebraic composition theorem to sit beneath the activation path. It does not, by itself, prove that the concrete quantized `signReLU8` or `softsign8` operators are Möbius. That stronger claim still requires actual in-tree activation definitions plus concrete finite Möbius witnesses. The SciSpace literature search supports the general composition perspective, including modular Möbius systems and neural-network Möbius composition, but it does not substitute for those local witnesses.

## Finite-state theorem class

For `_—→_`:

`Irreducible = ∀ s t → Reach _—→_ s t`.

`SelfLoop = ∀ s → s —→ s`.

`Irreducible × SelfLoop -> PeriodOne` is the reusable finite theorem package.

Exploration-only irreducibility never substitutes for full learner+EA reachability.

## Why the theorem loop is fast

The active carrier has exactly 256 Int8 codes, all masses are exact dyadic naturals, and the composition identities are finite definitional equalities. The remaining cost is kernel reduction over small finite structures rather than analysis over continuous domains. CI is the timing authority; no empirical benchmark is needed to establish the theorem ordering.

## Current emergent theorem for each permutation

Lazy Walk × MR15: full finite coupling theorem, generator support, self-loop, irreducibility, PeriodOne.

Lazy Walk × OpenES: same full finite coupling theorem class at the current shell.

Lazy Walk × Noisy Nets: the corresponding full coupling theorem plus the Noisy-Net softsign-gated transition factor.

Dyadic Ladder × MR15: the same full coupling class with the ladder law's additional power-of-two support.

Dyadic Ladder × OpenES: the same full coupling class with ladder support.

Dyadic Ladder × Noisy Nets: full coupling plus the Noisy-Net transition factor and ladder support.

Flat Dyadic × MR15: maximal law-support theorem at the base method level.

Flat Dyadic × OpenES: maximal law-support theorem at the base method level.

Flat Dyadic × Noisy Nets: the maximal connected theorem corner — maximal law support plus the strictly stronger representation-factor method theorem.

## Möbius status

Generic finite Möbius composition: proved.

Generic `signReLU8 -> softsign8` CHAD composition: proved.

Concrete activation-specific Möbius correspondence: not promoted until concrete in-tree activation semantics and witnesses exist.

## Replication order

Keep the three actual exploration methods and three remaining law modules distinct. Generate every law×method full composition. Attach the representation theorem at the softsign-gated boundary. Require Noisy-Net projection/lift for a strict coupled-method theorem. Keep Möbius composition exact and conditional on concrete activation witnesses. Let Agda `--safe` remain the final authority.
