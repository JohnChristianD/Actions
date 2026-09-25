# Thesis nomenclature and topology review — 2026-09-25

## Decision

The theorem topology is expanded along proof-bearing edges, and the economic interface is aligned with standard general-equilibrium vocabulary.

The canonical graph is:
canonical learner exact laws -> recurrent endomorphism/prefix correctness -> NormPair factor relation -> transition compatibility -> iterate compatibility -> F4 × NormPair factor stability.

The economic boundary remains explicit:
factor stability -> representation/factor structure only;
factor stability does not itself prove convergence, fixed-point existence, market clearing, or Walrasian equilibrium existence.

## Factor-stability terminology

The repository's NormPair relation is a dynamically preserved equivalence relation:
- states related by NormPair replacement have the same canonical policy;
- one canonical transition maps related states to related states;
- arbitrary finite iterates preserve the relation.

This is the precise content behind the thesis phrase "factor-stability". The result supports a quotient/factor dynamics interpretation: downstream policy dynamics can be reasoned about on equivalence classes, provided the relevant downstream observable respects the same relation.

It is not an equilibrium, compactness, coercivity, or convergence theorem.

## Production-side Walrasian coverage

The previous graph/docs already described a production-side path, but the active theorem source did not expose a proof-bearing production-economy contract under the exact literature-facing vocabulary. This branch adds:

- CompetitiveProductionEconomy
- ProductionSet
- CompetitiveWalrasianEquilibriumWithProduction
- consumer optimality, production feasibility, profit maximization, resource balance, and market clearing fields.

These are semantic contracts, not existence theorems. That distinction matters: the classical Arrow–Debreu production model uses production sets and profit-maximizing firms, together with additional structural assumptions, to obtain existence and welfare results.

## Literature naming policy

The older Mega-prefixed names are implementation-era names, not standard economic terminology. The branch therefore exposes GeneralizedWalrasianEquilibrium and generalizedWalrasianEquilibrium as the literature-facing names while retaining the underlying carrier for compatibility.

A blanket rename of every identifier in both monoliths is deliberately not performed. The learner monolith contains domain-specific implementation primitives (F4, NormPair, Watkins, GRU, exact scan, etc.) for which there is no one-to-one standard economics or topology literature name. Renaming those as if they were standard terms would make the thesis less, not more, accurate.

The correct convention is:
1. standard literature vocabulary at semantic/economic interfaces;
2. domain-specific names for the actual learner mechanisms;
3. explicit aliases where an implementation name has a standard literature interpretation;
4. graphs use the literature-facing concept names and point back to the exact Agda identifiers.

## Welfare boundary

The First Welfare route remains condition-gated. Equilibrium plus the required consumer/production assumptions can support Pareto optimality.

The Second Welfare route remains a separate supportability problem. Pareto optimality alone does not produce a supporting price/equilibrium witness in the generalized carrier. The repository's empty-price/empty-equilibrium countermodel is a non-derivability witness for the generalized semantic contract, not a refutation of the classical Second Welfare Theorem.

## Adviser-facing contribution

The defensible contribution is therefore not a new claim that classical Walrasian theory is false or that learner factor stability implies equilibrium. It is a machine-checked dependency topology that:

1. proves exact learner-side factor compatibility;
2. composes F4 and NormPair into an unconditional factor-stability theorem;
3. separates representation invariance from dynamical convergence;
4. exposes the production, market-clearing, price-support, and welfare assumptions needed to cross into economic equilibrium theory;
5. retains countermodels where a generalized contract is too weak to imply existence.

## Literature anchors

The production-side naming follows the standard competitive-equilibrium picture in which firms have production sets and maximize profits at prices, while consumers optimize subject to their budgets. Arrow–Debreu's production model explicitly represents each production unit by a set of feasible production plans and assumes structural properties such as closedness and convexity of production sets.

The first-welfare production formulation likewise uses profit maximization on the firm side together with consumer optimality and local nonsatiation/demand conditions.

The second-welfare production case is more delicate: supportability of Pareto optima depends on separation/supporting-price structure and production-side assumptions; dropping convexity can require substantially different hypotheses.

## Graph artifact

See:
.ci/discovery/f4-normpair-topology-production-welfare-2026-09-25.mmd

This graph intentionally distinguishes:
- exact theorem edges;
- factor/quotient structure;
- production-side equilibrium structure;
- welfare assumptions;
- non-implication/frontier edges.
