# Thesis contribution reassessment against the dedicated literature — 2026-09-25

## Scope

This note deliberately removes two claims from the thesis contribution story: machine-checked formalization is not itself novel, and choosing Agda rather than Lean is a methodological choice rather than a research contribution.

The contribution claim must instead be about the specific mathematical object, dependency boundary, and cross-domain formalization produced here.

## Econlib as the production-side reference

The production-side vocabulary is now benchmarked against Econlib's dedicated production-economy surface rather than against a loose generic Walrasian label.

Relevant Econlib objects include ProductionEconomy, RegularProductionEconomy, Technology, RegularTechnology, Technology.profit, Technology.supply, WalrasianEquilibriumWithProduction, and exists_equilibrium_prod, together with production-side First Welfare and Second Welfare results.

Econlib's production existence theorem is explicitly assumption-bearing. Its existence route supplies regularity, irreducibility, ownership/value conditions, and the associated production/consumer optimization structure. Therefore the local Agda semantic contract should not be presented as an unconditional existence theorem.

The local CompetitiveProductionEconomy / CompetitiveWalrasianEquilibriumWithProduction layer should be described as an interface contract whose fields mirror the economic ingredients: feasible production, profit maximization, consumer optimality, feasibility/resource balance, and market clearing. It is not the contribution to claim as a new production existence theorem.

## What is not the thesis contribution

Do not claim machine-checked economics, formalized Walrasian equilibrium, Agda formalization, a new production-side Walrasian existence theorem, a new First Welfare or Second Welfare theorem, or factor stability as a newly invented mathematical notion.

Each either already exists in the formalization ecosystem or is a standard mathematical pattern.

## Candidate substantive contribution 1: an explicit non-implication boundary

The strongest defensible contribution is the explicit formal separation of two theorem families that are easy to conflate:

exact learner identities / factor invariance -> representation-independent learner dynamics

does NOT imply convergence -> fixed point -> market clearing -> supporting price -> Walrasian equilibrium existence.

The monolith contains closed countermodels and impossibility statements that prevent those arrows from being silently promoted. The contribution is therefore an auditable dependency boundary for this particular learner/economic composition, not a new general-equilibrium theorem.

This becomes thesis-worthy if the dedicated literature review establishes that prior coupled learner/economic formalisms in the target literature leave these bridges implicit, untyped, or assumption-laden. That comparative claim still needs named prior systems as evidence.

## Candidate substantive contribution 2: a concrete quotient/factor result

The NormPair result is more specific than the generic statement that an equivalence relation is preserved. For this canonical learner, NormPair-related states have the same policy, the canonical transition preserves the relation, and arbitrary finite iterates preserve it.

This gives a quotient/factor interpretation of the learner dynamics. The mathematical pattern is standard; the candidate contribution is the exact characterization and proof for the chosen learner state and its consequences for downstream composition.

Use the phrase machine-checked quotient/factor characterization of the canonical learner's NormPair coordinate, not a new theory of factor stability.

## Candidate substantive contribution 3: a typed topology of missing economic obligations

The theorem/e-graph topology makes the missing bridges explicit and typed:

production primitives -> feasible firm plans -> profit-optimal supply;
supply + demand + resources -> aggregate balance -> market clearing;
separation/fixed-point structure -> supporting/derived price;
price + clearing + optimization -> generalized equilibrium;
generalized equilibrium + classical structural assumptions -> Arrow-Debreu specialization;
equilibrium + local nonsatiation/demand conditions -> Pareto optimality;
Pareto optimality -> supporting-price/redistribution result only with the separate Second Welfare assumptions.

This is not itself a new economic theorem. Its possible contribution is methodological: the formalization makes theorem dependencies and blocked implications machine-visible rather than leaving them as prose-level assumptions.

## Candidate substantive contribution 4: a generalized equilibrium interface

The generalized carrier is useful if it prevents classical specialization from being smuggled in as a primitive. The current design keeps generalized equilibrium, production structure, welfare, Arrow-Debreu specialization, and existence as distinct interfaces and edges.

The architectural contribution can therefore be stated as: a coupled learner/economic formalization can expose a generalized equilibrium interface while retaining explicit, typed obligations for production, market clearing, price support, convergence, and classical specialization.

## Production-side interpretation

For the pure unconditional production surface, the right thesis language is:

The formalization provides a closed semantic contract for competitive production equilibrium ingredients and a closed impossibility result showing that such a generalized contract does not, by itself, entail an equilibrium witness.

The singleton empty-equilibrium countermodel is a local non-derivability witness. It is not a refutation of Arrow-Debreu or Econlib. Classical existence theorems add the structural hypotheses that the local generalized carrier intentionally leaves open.

## The real research question

The thesis should move away from: Can Agda machine-check a learner/economic model?

Toward: Which economic conclusions are actually entailed by the exact learner dynamics and which require independent economic assumptions, and can that boundary be represented as a mechanically auditable dependency topology?

That question is where the existing F4/NormPair proofs, production interface, countermodels, and economic graph fit together.

## Current import/CI synchronization

No Agda import declarations are changed by this reassessment.

The existing Dhall orchestration already compiles both monoliths with the same Agda environment: --safe, standard-library, and the repository root include path. The theorem monolith imports the learner monolith as C; the learner does not import the theorem monolith. This is the correct dependency direction and remains unchanged.

The synchronization requirement is therefore satisfied by the current import surface rather than by adding or rewriting imports. Future changes should preserve this one-way dependency.

## Adviser-facing contribution statement

The thesis does not claim novelty from formal verification, Agda, or from re-proving classical Walrasian results. Its substantive contribution is a mechanically auditable dependency topology for a specific coupled learner/economic system. The formalization identifies and proves the learner-side invariance and quotient structure that actually follow from the model, while explicitly blocking convergence, fixed-point, market-clearing, supporting-price, and equilibrium-existence conclusions unless their independent economic hypotheses are supplied. On the production side, it aligns the semantic interface with the standard competitive-production/Walrasian vocabulary and records the corresponding optimization and market-clearing obligations without silently importing an existence theorem. The resulting contribution is the explicit characterization of what the coupled model entails, what it does not entail, and where classical economic assumptions enter.

## Novelty standard

Before final thesis wording, compare this exact dependency-boundary claim against formalized general-equilibrium libraries such as Econlib; formalized welfare/existence developments; computational economics and learning-in-markets literature that couples learning dynamics to equilibrium concepts; quotient, bisimulation, and congruence results for dynamical systems and reinforcement-learning state abstractions; and formal dependency, e-graph, or proof-graph approaches in adjacent formal-methods work.

The final novelty claim should be limited to the intersection that the prior literature does not already cover.