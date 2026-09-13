# Theorem-first finite ERL/EA replication wiki

Authority: Agda `--safe`.

Repository CI checks the canonical source, finite exploration kernels, admissible dyadic laws, the softsign-gated representation factor, finite CHAD/Möbius composition modules, and the generated law×method theorem surface.

## Actual exploration methods

Exactly three actual exploration methods are admitted:

1. MR15 — `Exotic/ERL/Exploration/MR15Reachability.agda`
2. OpenES — `Exotic/ERL/Exploration/OpenESDyadic.agda`
3. Noisy Nets — `Exotic/ERL/FullCoupled/NoisyNetCoupled.agda`

Probability laws are parameters to those methods, not separate explorers.

## Permanent law pruning

The former triangular law is permanently absent from the selectable theorem surface.

Flat Dyadic is also permanently pruned. Under the retained admissibility class it is redundant: it contributes complete code support but no scale-geometric shell theorem, while the present target class is explicitly finite, symmetric, unimodal, scale-geometric, aperiodic, irreducible, and dyadic.

The retained exact finite laws are:

- Lazy Walk: weights `2,1,1` over `{0,+1,-1}`, denominator `4`.
- Dyadic Ladder: weight `16` at zero and weight `1` on each signed power-of-two shell through `±128`, denominator `32`.
- Dyadic Geometric 5: weights `66,16,16,8,8,4,4,2,2,1,1` over `{0,±1,…,±5}`, denominator `128`.

Dyadic Geometric 5 is the new contiguous scale-geometric law: its nonzero shell mass halves at every radius, it is symmetric and strictly unimodal on contiguous integer support, it has positive zero mass for the self-loop theorem, and it has positive ±1 mass for the `Z_256` generator theorem.

Natural rejected candidates have direct theorem obstructions. Rademacher-only support omits zero and therefore loses the one-step self-loop witness. Even-step support has nontrivial gcd with `256` and therefore cannot generate the full additive torus. Other sparse laws lacking a small generator need additional generator proofs and are not stronger under the current exact interface.

## Canonical representation boundary

Exploration is attached to the softsign-gated representation layer.

The forward algebra remains:

`E -> RoPE -> Pyr^top-k -> Fastfood_frozen -> signReLU8 -> softsign8 -> GateNN -> Pi`.

Concrete finite activation definitions are in `Exotic/ERL/Finite/Activation.agda`.

`Exotic/efficient_chad/SoftsignGatedComposition.agda` proves the exact CHAD composition law for finite `softsign8 ∘ signReLU8`. This is a genuine forward/pullback composition theorem.

`Exotic/efficient_chad/MobiusInt8Composition.agda` proves exact composition closure for finite homogeneous-coordinate actions. It still does not certify the concrete quantized `signReLUQ8` and `softsignQ8` pair as one global Möbius action. That activation-specific promotion remains conditional on a concrete finite Möbius witness.

## Why MR15 and OpenES were previously identical

They were literally the same theorem shell because both had been encoded as arbitrary fresh-target relations over the same kind of small finite surrogate. Their irreducibility and self-loop proofs were therefore isomorphic copies.

That abstraction is now separated:

- OpenES is the scalar `Int8` quotient.
- MR15 is the two-coordinate `SoftsignGatedRepresentation` state.

The MR15 projection forgets its second coordinate and the section restores it at zero. The strict witness is `(1,0)` versus `(1,1)`: identical OpenES projection, distinct MR15 state.

## Noisy-Net strict extension

`Exotic/ERL/FullCoupled/SoftsignGatedRepresentation.agda` gives the canonical factor from full Noisy-Net state to the softsign-gated representation. The projection preserves the visible gate signal and learner signal and forgets `sigma3`; the section sets `sigma3` to zero.

Two full states can therefore have the same representation but differ in `sigma3`. This makes Noisy Nets a proper extension of the representation theorem state, rather than merely carrying more lemmas.

## Real strict theorem ordering

The method ordering is induced by actual factor maps and theorem transfer:

`OpenES < MR15 < NoisyNet`.

The first strict link transfers `PeriodOne(MR15Step)` to `PeriodOne(openESStep)` through the MR15 projection/lift and has a proper-fiber witness.

The second strict link transfers `PeriodOne(NoisyNetStep)` to `PeriodOne(MR15Step)` through the Noisy-Net representation factor and has the hidden-`sigma3` proper-fiber witness.

Thus Noisy Nets is the strict method maximum in the current theorem preorder. No statistical quantity enters this ordering.

The law axis remains a partial order. Lazy Walk has minimal local support; Dyadic Geometric 5 has strictly richer contiguous geometric support; Dyadic Ladder has incomparable sparse multiscale support. A total law ordering would require an additional formal criterion and is deliberately not fabricated.

## Full emergent theorem for each retained permutation

Each generated object has type `FullAlgebraicCoupling law step`, so the theorem only appears after exact law normalization/unit-support, concrete forward/pullback composition, irreducibility, self-loop, and derived `PeriodOne` have been composed.

Lazy Walk × MR15: full softsign-gated representation coupling theorem.

Lazy Walk × OpenES: full scalar quotient coupling theorem.

Lazy Walk × Noisy Nets: full coupled theorem plus the strict NoisyNet-to-representation factor.

Dyadic Ladder × MR15: full representation theorem with ladder support witnesses.

Dyadic Ladder × OpenES: scalar full theorem with ladder support.

Dyadic Ladder × Noisy Nets: full coupled theorem plus the NoisyNet factor and ladder support.

Dyadic Geometric 5 × MR15: full representation theorem with contiguous symmetric scale-geometric support.

Dyadic Geometric 5 × OpenES: scalar full theorem with the same geometric law.

Dyadic Geometric 5 × Noisy Nets: strongest retained full-coupling theorem on the method axis combined with the retained contiguous geometric law.

## Automation

`.ci/discovery/ExplorationTheoremGenerator.hs` enumerates exactly nine method×law permutations. Haskell only constructs source and runs `agda --safe`; Agda is the theorem acceptance oracle.

The kernel should be fast because the active carrier is finite Int8 and all probability masses and algebraic identities reduce over finite exact constructors. CI is the timing authority and no benchmark is used to define theorem strength.

## Current validation signal

A completed canonical run passed the permanent scope guard, canonical source, regression, MR15, OpenES, and NoisyNet gates; the pre-refactor failure was the Lazy Walk `_+_` import, which is fixed. The new geometric law, flat-law removal, representation-boundary refactor, and strict-factor theorem require the fresh canonical run on the current head before being called green.

## Replication order

Keep methods and laws separate. Explore at the softsign-gated representation boundary. Generate every retained law×method full composition. Require concrete projection/lift theorems before strict method comparison. Treat Möbius closure as generic until activation-specific witnesses are actually proven. Let Agda `--safe` remain the final authority.
