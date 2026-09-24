# NormPair quotient/factor transition closure

The theorem monolith now contains CanonicalNormPairQuotientFactorTransitionTheorem.

Exact relation:

- normPairReplacementRelation s t = Sigma NormPair (replaceNorm s n == t).
- applyNormPairReplacements generates the relation; finite replacement lists collapse to one final NormPair replacement.
- The relation is reflexive, symmetric, and transitive.
- canonicalPolicy factors through the relation by the existing exact canonicalPolicy-norm-invariant.
- canonicalFullStep respects the relation through canonicalFullStep-replaceNorm.
- Iterated canonical transitions respect the relation through the existing iterate-commutation law.

This closes the NormPair quotient/factor transition seam as an actual Agda proof surface.

The stronger CanonicalEndogenousHardSignFactorAutomatonClosureCandidate remains a frontier. The missing parts are a finite invariant factor preserved by HardSign, an affine realization of arbitrary finite automaton transitions, a nontrivial finite-factor witness, and the connected nonrepresentability witness required by the repository separation contract.

The same patch records an explicit negative boundary for unconditional generalized Walrasian existence. MegaGeneralizedWalrasianEquilibrium permits an arbitrary equilibrium predicate, including an empty predicate, so the contract alone cannot yield a universal existence theorem. Classical Walrasian existence requires model-specific economic assumptions and a proof connecting them with this generalized contract.

Kernel authority remains Agda --safe; fresh CI verification is the remaining machine check for this branch.
