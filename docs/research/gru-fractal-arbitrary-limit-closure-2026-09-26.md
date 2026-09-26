# Arbitrary-limit closure for GRU-injective fractal composition — 2026-09-26

## Summary

The finite/indexed fractal kernel does not by itself justify an arbitrary-depth or limit-level injectivity theorem. This change makes that boundary explicit.

The new FractalLimitClosure contract separates three facts: each indexed representation is an approximation to a limit representation; the approximation relation is witnessed for every level; and the limit representation is separating/injective on the state carrier.

The resulting fractalLimitInjective theorem is therefore conditional on an explicit limit-separation witness. Convergence or completeness alone is not promoted to injectivity.

## Exact graph closure

GRU decode-after-encode
→ local injectivity
→ level-indexed injectivity
→ injective inter-level transport
→ transport/encoding compatibility
→ finite/indexed GRU-injective fractal composition
→ compatible approximation sequence
→ existence of a limit representation
→ limit separation / uniqueness
→ arbitrary-limit GRU-injective closure

The last implication is deliberately split. A limit may exist while distinct states become indistinguishable at the limit. Thus finite-level injectivity plus convergence does not imply limit injectivity.

A positive limit theorem needs an additional separation mechanism, for example a uniform lower bound, an injective limit operator, a left inverse that survives the limit, or another domain-specific observability theorem.

## Navier–Stokes relevance audit

The current September 2026 Navier–Stokes AI result is useful as a boundary example, not as a missing premise for the fractal theorem.

OpenAI's public Lean repository formalizes finite-time blow-up results for smooth forced 3D incompressible Navier–Stokes on both Euclidean space and the periodic torus. Its formalization metadata reports zero sorry counts for the listed main results and records the Lean axioms used by those theorem declarations. The repository also provides Comparator challenge material for independent checking.

This is algebraically compatible with the repository's methodology in one important sense: the external result is exposed as typed Lean propositions rather than being treated as an informal AI claim. However, it is not a direct algebraic inhabitant of FractalInjectiveComposition or FractalLimitClosure.

The useful transferable pattern is PDE dynamics → finite-time singularity / failure of global smooth continuation → explicit obstruction to an assumed global limit or continuation theorem.

It does not establish a limit of the repository's GRU encodings, convergence of the learner trajectory, uniqueness of a representation limit, injectivity of a limit representation, a global fixed point, market clearing, or equilibrium.

## Algebraic-consistency assessment

The public Lean formalization is structurally consistent with the typed-proof approach: its top-level Navier–Stokes file imports the formalized result modules, and the repository states that the build uses Lean 4.34.0-rc2, Mathlib, and Lake. The main result declarations are explicit existential/non-existence propositions rather than prose claims.

That is strong evidence of machine-checkable consistency of the published Lean artifacts, but it is not an independent mathematical audit of every analytic argument. The repository itself reports the proof-assistant axioms propext, Classical.choice, and Quot.sound for the main results.

For this repository, the result is therefore best used as a limit/continuation boundary reference, not imported as an Agda theorem or used as evidence that fractal limits preserve injectivity.

## Formal boundary

GRUFractalLimitClosure.agda intentionally does not manufacture a convergence theorem. It makes the missing mathematical obligation visible as limitSeparation.

The next genuinely stronger step would be to instantiate a metric/topological limit carrier and prove a non-collapse/separation theorem for the specific GRU representation. That should only be promoted to an unconditional theorem after its hypotheses are formalized and checked.

## Verification intent

The module is --safe and belongs beside the existing generic fractal composition kernel. The discovery graph is explanatory; the Agda contract is authoritative for the formal boundary.
