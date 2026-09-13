# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

Repository CI checks the canonical source, finite exploration kernels, admissible dyadic laws, the softsign-gated representation factor, finite CHAD/Möbius composition modules, and the generated law×method theorem surface.

## Actual exploration methods

There are exactly three actual exploration methods:

1. MR15 — `Exotic/ERL/Exploration/MR15Reachability.agda`
2. OpenES — `Exotic/ERL/Exploration/OpenESDyadic.agda`
3. Noisy Nets — `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

Probability laws are parameters to those methods. Lazy Walk and Dyadic Ladder are not explorers.

## Permanent law pruning

The former triangular law is permanently absent from the selectable theorem surface.

Flat Dyadic is also permanently pruned. Under the retained admissibility class, it is redundant: it gives full code support but contributes no scale-geometric shell law, so it does not strengthen the structural theorem class being targeted.

The retained exact finite laws are:

- Lazy Walk: weights `2,1,1` over `{0,+1,-1}`, denominator `4`.
- Dyadic Ladder: weight `16` at zero and weight `1` on each signed power-of-two shell through `±128`, denominator `32`.
- Dyadic Geometric 5: weights `66,16,16,8,8,4,4,2,2,1,1` over `{0,±1,…,±5}`, denominator `128`.

The geometric law is the new contiguous scale-geometric candidate. Its nonzero shells halve exactly with radius, it is symmetric, strictly unimodal on contiguous integer support, dyadic, has positive zero mass for a self-loop, and has positive ±1 mass for the `Z_256` generator witness.

Other natural candidates are pruned from the strict admissible class by theorem obstruction: Rademacher-only laws have no zero step and therefore lack the self-loop needed for the one-step period theorem; even-step laws have `gcd(256,S) > 1` and therefore cannot generate the full 256-state additive torus; support families missing ±1 require a different generator witness and are not minimal under the present theorem interface.

## Canonical representation boundary

Exploration is now attached to the softsign-gated representation layer.

The forward algebra remains:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

The concrete finite activation definitions are in `Exotic/ERL/Finite/Activation.agda`.

`Exotic/efficient_chad/SoftsignGatedComposition.agda` proves the exact CHAD composition law for the finite `softsign8 ∘ signReLU8` operator. This is a genuine forward/pullback composition theorem.

The current Möbius module, `Exotic/efficient_chad/MobiusInt8Composition.agda`, proves exact finite action composition, but it does not yet certify the concrete quantized activation pair as one global Möbius action. That promotion requires concrete finite Möbius witnesses for the actual activation semantics, and is therefore kept conditional.

## Why MR15 and OpenES were previously identical

They were previously the same theorem because both were encoded as arbitrary fresh-target relations over essentially the same small finite surrogate. Their constructor proofs were therefore isomorphic copies of the same irreducibility and self-loop argument.

That abstraction has now been separated:

- OpenES is the scalar `Int8` quotient.
- MR15 is the two-coordinate `SoftsignGatedRepresentation` state.

A concrete projection/lift factor carries MR15 down to OpenES. The projection forgets the second representation coordinate, and the section restores it at zero. The strict witness is the pair of states `(1,0)` and `(1,1)`: they have the same OpenES projection but are distinct MR15 states.

## Noisy-Net strict extension

`Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda` provides the canonical factor from full Noisy-Net state to the softsign-gated representation:

`projectSoftsignGated : CoupledNoisyNetState -> SoftsignGatedRepresentation`

with a section/lift and a retraction theorem. The projection forgets `sigma3`, while preserving the visible gate signal and learner coordinate.

The strict witness uses two states with identical visible representation and different `sigma3`. Thus the full Noisy-Net state is a proper extension of the representation state.

This is the missing theorem bridge that was required before calling Noisy Nets strictly stronger than representation-layer exploration.

## Real strict theorem ordering

The current ordering is no longer a tag or witness-count ranking. It is induced by actual theorem implication through state factors:

`OpenES < MR15 < NoisyNet`.

The two strict links are:

`PeriodOne(MR15Step) -> PeriodOne(openESStep)` through the MR15 projection/lift factor, with a proper-state witness showing the factor loses a real coordinate.

`PeriodOne(NoisyNetStep) -> PeriodOne(MR15Step)` through the NoisyNet-to-softsign representation factor, with a proper-state witness showing that `sigma3` is a genuinely hidden coordinate.

Therefore the method axis has a genuine strict theorem maximum at Noisy Nets, not merely a larger bundle of witness lemmas.

The law axis is deliberately only partially ordered. Lazy Walk has minimal `{0,±1}` support; the geometric law has a strictly richer contiguous scale-geometric support; Dyadic Ladder has multiscale shell support that is incomparable with contiguous geometric support. A total law ranking would require adding a new formal criterion. No empirical/statistical comparison is used.

## Full emergent theorem for every ablation

Each generated object is a `FullAlgebraicCoupling law step`, so the theorem is emitted only after exact law facts, the finite activation forward/pullback composition, the actual explorer transition, and the graph theorem are all composed.

Lazy Walk × MR15: full finite representation-layer coupling, irreducibility, self-loop, and PeriodOne.

Lazy Walk × OpenES: the scalar quotient version of the same full coupling theorem.

Lazy Walk × Noisy Nets: full coupled theorem plus the concrete factor to the softsign-gated representation; this is strictly above the MR15 theorem class.

Dyadic Ladder × MR15: full representation-layer theorem with the ladder support witnesses.

Dyadic Ladder × OpenES: scalar full-coupling theorem with the same ladder law.

Dyadic Ladder × Noisy Nets: full coupled theorem plus the Noisy-Net representation factor and ladder support witnesses.

Dyadic Geometric 5 × MR15: full representation-layer theorem with contiguous symmetric scale-geometric dyadic support.

Dyadic Geometric 5 × OpenES: scalar full-coupling theorem with the same geometric law.

Dyadic Geometric 5 × Noisy Nets: the strongest method theorem class currently admitted, combined with the strongest retained contiguous scale-geometric law.

## Automated theorem generation

`.ci/discovery/ExplorationTheoremGenerator.hs` enumerates exactly nine law×method permutations:

`{MR15, OpenES, NoisyNet} × {LazyWalk, DyadicLadder, DyadicGeometric5}`.

Haskell only constructs the proof harness. Agda `--safe` is the acceptance oracle. The generator also imports the strict method-order theorem surface so the generated report contains the actual factor-induced ordering rather than a hard-coded level tag.

## Why the kernel should be fast

The active numeric carrier is finite Int8, the law masses are exact natural numerators over powers of two, and the main algebraic identities reduce definitionally. This makes the theorem checks small finite reductions rather than continuous analytic proofs. CI is the runtime authority; no performance ranking is inferred from wall-clock timing.

## Current automated status

The last canonical run before the latest refactor passed the permanent scope guard, canonical source, canonical regression, MR15, OpenES, and NoisyNet checks, then stopped at the Lazy Walk law because `_+_` was not imported into that module. That import has since been fixed. A fresh run is required for the new geometric-law, factor-order, and pruned-file surface.

## Replication order

Keep method and law interfaces separate. Attach exploration to the softsign-gated representation state. Generate every retained law×method full composition. Require concrete projection/lift factors before claiming strict method dominance. Treat finite Möbius composition as a generic closure theorem until concrete activation witnesses close the activation-specific gap. Let Agda `--safe` remain the final authority.
