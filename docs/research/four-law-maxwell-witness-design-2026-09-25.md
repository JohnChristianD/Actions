# Four-law Maxwell witness design — 2026-09-25

## Purpose

Freeze the concrete semantic boundary before adding Agda witness code. This note records what the existing Hodge-Maxwell surface can provide, what classical Maxwell/variational semantics support, and which exact repository fields remain uninhabited.

## Existing repository carriers

The existing exact Hodge-Maxwell representation exposes:

- `Solution` as the physical solution carrier;
- `fieldF : Solution → Form2`;
- `fieldJ : Solution → Form3`;
- Maxwell equations `d (fieldF s) ≡ zero3` and `dStar (star (fieldF s)) ≡ fieldJ s`;
- a physical `step : Solution → Solution`;
- a GRU-side step and a learner-facing `encode/decode` inverse pair with one-step conjugacy;
- continuity obligations for the differential-form operations, solution fields, and steps.

This makes `Solution` the only justified candidate for the Law-I/Law-III `PhysicalState` at this stage. Introducing a parallel physical carrier would create a second representation seam that is not required by the current proof surface.

## Law-I candidate boundary

Candidate mapping:

- `PhysicalState = Solution`;
- `Current = Form3`;
- `current = fieldJ`;
- `trajectory` must be a concrete physical evolution on `Solution`, preferably the existing `step` when its semantics match the intended trajectory;
- required proof obligation:
  `∀ p → fieldJ (trajectory p) ≡ fieldJ p`.

The important point is that Maxwell current conservation is not automatically the same proposition. nLab's conserved-current formalism defines conservation as horizontal closure on the covariant phase space, while its Maxwell material uses differential-form Maxwell equations and an electromagnetic current. These support the semantic vocabulary, but the repository contract asks for current preservation across its chosen trajectory. A theorem connecting the existing `step` to current preservation must therefore be proved explicitly.

If the existing `step` does not preserve `fieldJ`, the correct outcome is to introduce a separately justified trajectory map and prove its current compatibility, not to assert an equality merely because `d j = 0` holds.

Primary sources:
- https://ncatlab.org/nlab/show/conserved%2Bcurrent
- https://ncatlab.org/nlab/show/Maxwell%27s%2Bequations

## Law-III candidate boundary

Candidate mapping:

- `PhysicalState = Solution`;
- `Variation` must represent a genuine field variation, not a constant placeholder;
- `Action` must represent a genuine action/Lagrangian datum for the selected Maxwell model;
- `Admissible : Variation → Set` must encode the boundary/constraint conditions under which the variation is allowed;
- `Stationary : Solution → Set` must encode a proved critical-point/Euler–Lagrange condition;
- required proof obligation for every selected physical state:
  `Stationary p`.

The classical electromagnetic route is the free Maxwell action with a potential 1-form A, field strength F = dA, and the Euler–Lagrange equation corresponding to the Maxwell equation for d star F. The repository currently does not expose enough action/variation/Euler–Lagrange primitives to claim that this mapping is already an Agda inhabitant.

Therefore the implementation must first identify or add the smallest genuine variational data structure compatible with the existing `Solution` carrier. A trivial variation or an unconstrained `⊤)-valued stationarity predicate is explicitly out of scope because it would satisfy the type while losing the Law-III semantics.

Primary sources:
- https://ncatlab.org/nlab/show/action%2Bfunctional
- https://ncatlab.org/nlab/show/variational%2Bbicomplex
- https://ncatlab.org/nlab/show/geometry%2Bof%2Bphysics%2B--%2Bperturbative%2Bquantum%2Bfield%2Btheory

## Learner bridge

The existing theorem `canonical-physics-to-learner-transition-witness` is the intended bridge. It is conditional on `CanonicalLearnerHodgeMaxwellCompositionTheorem` and supplies a learner-to-solution encode/decode pair plus one-step conjugacy.

This means the specialized Maxwell witness should reuse that adapter rather than duplicate learner/solution inverse proofs. The remaining alignment question is whether the concrete `Solution` chosen above is definitionally the same solution carrier used by the theorem instance at the point where the final witness is constructed.

## Exact blocker after boundary freeze

The existing repository is not yet sufficient to construct a truthful `FourLawOneStepWitnessContract` from these semantics alone. Two concrete proof surfaces remain to be built:

1. a trajectory/current theorem on the selected `Solution` carrier;
2. a nontrivial Maxwell variational layer with admissibility and stationarity proofs on that same carrier.

Until both exist, the graph must remain `FRONTIER_CONTRACT_ONLY`, and iterate/prefix/e-graph kernels remain transport infrastructure rather than closure evidence.

## Provenance

- Repository authority: `Exotic/ERL/FullCoupled/FourLawClosureWitnesses.agda` and `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`.
- Plan: `docs/superpowers/plans/2026-09-25-four-law-maxwell-witnesses.md`.
- External semantic sources: the nLab pages listed above.
- Knowledge delta: this file freezes the carrier mapping and records the exact unresolved proof obligations before production witness code.


## Task 2 audit — exact Law-I blocker

A direct audit of the current theorem surface shows that the existing Hodge-Maxwell record provides a physical `step : Solution → Solution` and the observable `fieldJ : Solution → Form3`, but no theorem establishing

`∀ p → fieldJ (step p) ≡ fieldJ p`.

The existing Maxwell closure field only establishes that the stepped solution satisfies the Maxwell equation again; it does not imply preservation of the chosen current observable. Therefore the Law-I witness cannot honestly be constructed by taking the existing `step` as trajectory.

The tempting alternatives are not acceptable: identity trajectory would satisfy the equality definitionally but would not be the intended physical evolution, and replacing the equality with a differential conservation statement would weaken the repository contract.

Consequently Task 2 remains blocked on one concrete mathematical theorem: **current preservation for the selected physical trajectory**. No Agda witness module was added merely to encode this missing premise.

This is a deliberate red boundary, not a failed implementation: the implementation plan explicitly requires the exact equality and forbids synthetic witnesses.
