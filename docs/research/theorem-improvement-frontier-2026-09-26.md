# Theorem improvement frontier — 2026-09-26

The current theorem monolith is already explicit about proof boundaries. The highest-value improvements are generalizations of existing proof interfaces rather than stronger conclusions without premises.

## Search result

The 2026 Isabelle/AFP Equality Saturation Checker formalizes checking e-graph merge and extraction certificates and separates executable graph machinery from checked proof objects. citeturn0search2 Equality saturation is also established as a proof-assistant tactic, while recent versioned e-graph work targets conditional reasoning and proof-by-cases. citeturn0search10turn0search3 Classical production-side equilibrium existence is assumption-heavy: Arrow–Debreu's integrated production/exchange/consumption theorem makes economic premises explicit. citeturn0search58turn0search59

## Recommended theorem upgrades

### A. Generic strict progress
Generalize StrictProgressWitness beyond the current Nat instantiation. Prove cycle exclusion once from a suitable strict/well-founded progress relation, then instantiate it with totalCount.

### B. Explicit factor transition
The NormPair surface already proves policy invariance, one-step transition compatibility, and iterated compatibility. The next theorem should expose an observation q into a factor carrier, prove that q respects the replacement relation, construct the induced factor transition, and prove policy/readout factorization through q.

### C. Generic commuting-square transport
Unify the existing encode/decode and one-step commuting-square patterns into one generic theorem: inverse laws plus one-step commutation imply iterate transport; a separate theorem transports invariants/properties. This becomes the common kernel for learner, Hodge-Maxwell, Tsallis, economics, and POMDP transport.

### D. Production-side assumption records
Expose production feasibility, firm optimality, consumer optimality, aggregate feasibility, market clearing, supporting price, and Walrasian equilibrium as distinct witnesses. This aligns the formal vocabulary with classical production/equilibrium literature without importing hidden assumptions. citeturn0search58turn0search59

### E. Distributional stationary-law bridge
Keep deterministic state convergence separate from distributional convergence: distribution-valued orbit → limit witness → transition-preserved limit → stationarity → stationary economic aggregate.

### F. Certificate-carrying graph edges
Extend PROVED / CONDITIONAL / FRONTIER / BLOCKED with assumptions, proof identifier, source language, constructive-vs-discovery flag, and unconditionality flag. This matches the direction of certified equality-saturation work. citeturn0search2turn0search3

## Priority

1. Generic strict-progress exclusion.
2. Explicit quotient/factor transition.
3. Generic encode/decode commuting-square transport.
4. Assumption-carrying production/equilibrium interfaces.
5. Context-aware proof-certificate graph edges.
6. Distributional stationary-law bridge.

These strengthen the theorem architecture without introducing a hidden Fin n assumption and without changing the Set-polymorphic cross-domain carrier design.
