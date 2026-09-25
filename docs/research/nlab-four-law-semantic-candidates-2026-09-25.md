# nLab semantic candidates for four-law closure

Date: 2026-09-25

## Research question

Can nLab provide concrete mathematical semantics that can legitimately inhabit the repository's missing Law-I trajectory/current witness and Law-III variational witness, without weakening those contracts or inventing axioms?

## Findings

### Law I: conserved current is the right semantic vocabulary, but not yet the repository witness

nLab defines a conserved current as an (n-1,0)-form that is horizontally closed on the covariant phase space, and states that homologous hypersurfaces carry the same integrated charge. Noether's theorem supplies conserved currents from symmetries of a Lagrangian. In electromagnetism, nLab identifies the electric current j_el by d star F = j_el and derives d j_el = 0, so the associated charge is independent of the choice of spacelike hyperslice.

Primary sources:
- https://ncatlab.org/nlab/show/conserved%2Bcurrent
- https://ncatlab.org/nlab/show/Noether%27s%2Btheorem
- https://ncatlab.org/nlab/show/electric%2Bcharge
- https://ncatlab.org/nlab/show/electromagnetic%2Bfield

The repository's LawIPhysicsWitness asks for the stronger discrete compatibility statement current (trajectory p) = current p. Therefore nLab's conservation law is a viable semantic source for a concrete Law-I model, but an Agda adapter still has to choose what PhysicalState, Current, and trajectory mean and prove the required compatibility. A local conservation equation by itself is not silently promoted to that equality.

### Law III: classical variational calculus supplies the exact semantic vocabulary

nLab describes classical field theory using an action functional on a configuration/history space. Variations are represented by the variational differential; the Euler-Lagrange form vanishes exactly on the solution/critical locus. nLab's Noether discussion also explains the role of boundary-vanishing/admissible variations and the derivation of Euler-Lagrange equations from stationarity of the action.

Primary sources:
- https://ncatlab.org/nlab/show/action%2Bfunctional
- https://ncatlab.org/nlab/show/variational%2Bcalculus
- https://ncatlab.org/nlab/show/Euler-Lagrange%2Bform
- https://ncatlab.org/nlab/show/Euler-Lagrange%2Bequation
- https://ncatlab.org/nlab/show/Noether%27s%2Btheorem
- https://ncatlab.org/nlab/show/variational%2Bbicomplex

This maps naturally to the repository's Law-III contract: a concrete model can supply an action/Lagrangian, an admissibility predicate for variations, and a stationarity predicate corresponding to the Euler-Lagrange shell. The contract still requires an actual inhabitant, so these definitions alone are not a proof.

### Maxwell theory is a promising concrete Law-II/Law-III bridge

nLab explicitly states that Maxwell's equations are Euler-Lagrange equations for a free electromagnetic Lagrangian. It gives the vacuum equation d star F = 0 and, more generally, the sourced Maxwell equation d star F = j. This is useful because the repository already has an exact Hodge-Maxwell representation surface.

Primary sources:
- https://ncatlab.org/nlab/show/A%2Bfirst%2Bidea%2Bof%2Bquantum%2Bfield%2Btheory%2B--%2BLagrangians
- https://ncatlab.org/nlab/show/Euler-Lagrange%2Bequation
- https://ncatlab.org/nlab/show/Maxwell%27s%2Bequations
- https://ncatlab.org/nlab/show/Hodge-Maxwell%2Btheorem

The important limitation is that this still does not provide the repository-specific learner-to-physical inverse or discrete one-step conjugacy. It gives a principled candidate physical semantics from which those adapters could be constructed.

## Candidate semantic route

The least-assumptive route identified by this search is:

1. Use a concrete classical electromagnetic field model already compatible with the repository's Hodge-Maxwell carrier.
2. Define Law III from its action/Lagrangian, admissible variations, and Euler-Lagrange shell.
3. Define Law I using the model's conserved current and a trajectory/evolution operation, with the required current-preservation theorem stated at the repository's PhysicalState to Current level.
4. Prove the learner-to-physical inverse and transition conjugacy against the existing Hodge-Maxwell representation rather than inventing a second unrelated physical carrier.
5. Only then instantiate FourLawOneStepWitnessContract and apply the existing iterate/prefix/e-graph transport kernels.

## What this research does not establish

This nLab search does not establish an inhabited LawIPhysicsWitness or LawIIIVariationalWitness in Agda. It identifies an appropriate semantic model and the mathematical obligations needed to build those witnesses. The repository's current frontier therefore remains honest: concrete semantics are now better specified, but four-law closure is not yet proved.

## Design constraint

Do not weaken current (trajectory p) = current p into an unrelated conservation slogan, and do not use a zero/trivial variation merely to populate LawIIIVariationalWitness. The implementation must preserve the intended physical meaning of the contracts.