# Thesis contribution reassessment against the dedicated literature — 2026-09-25

## Bottom line

The thesis should not claim novelty from machine checking, Agda, or re-formalizing Walrasian equilibrium. Econlib already provides a substantial Lean formalization of general equilibrium, including Walrasian existence, welfare, Walras' law, and an Arrow–Debreu production layer. Its glossary explicitly exposes ProductionEconomy, RegularProductionEconomy, Technology, Technology.profit, Technology.supply, production-side welfare theorems, and ProductionEconomy.exists_equilibrium_prod.

The defensible research question is instead: which economic conclusions are actually entailed by the exact learner dynamics, which are independent economic obligations, and can that boundary be represented as a mechanically auditable dependency topology?

## Dedicated literature comparison

### 1. Formal general equilibrium

Econlib is the direct benchmark for the production-side vocabulary and formalization baseline. It contains a standard production economy with technology/profit/supply, Walrasian equilibrium with production, production-side welfare results, and an existence theorem built from explicit structural hypotheses.

Implication for this thesis: the local Agda production surface is not a new Walrasian existence theorem. It is valuable only insofar as it preserves the distinction between an abstract equilibrium contract and the additional assumptions required for existence.

Reference: https://github.com/danlyng/Econlib

### 2. Learning and equilibrium

The economics literature already studies learning processes precisely in relation to equilibrium and emphasizes that convergence depends on the learning rule and game class. Fudenberg and Levine's survey frames learning as a nonequilibrium process whose long-run behavior can or cannot correspond to equilibrium. Viossat and Zapechelnyuk connect no-regret dynamics with fictitious play and establish convergence results only for specified classes of games. Recent work continues to organize regret, learning, and equilibrium around explicit dynamical assumptions.

Implication for this thesis: the learner-to-equilibrium boundary is not novel merely because learning and equilibrium are connected. The candidate contribution is the formal, model-specific statement of which bridges are absent from this particular learner and therefore cannot be silently inferred.

References:
- https://www.annualreviews.org/content/journals/10.1146/annurev.economics.050708.142930
- https://doi.org/10.1016/j.jet.2012.07.003
- https://arxiv.org/abs/2608.09389

### 3. State abstraction and quotient dynamics

State equivalence, abstraction, and quotienting are established subjects in AI and dynamical decision systems. Givan, Dean, and Greig give a bisimulation-based equivalence for MDP state aggregation under which an optimal policy on the reduced model induces a corresponding policy on the original model. Abel's state-abstraction program likewise studies when abstractions preserve useful behavior.

Implication for this thesis: calling the NormPair result a new abstraction theory would be incorrect. The narrower contribution is the exact quotient/factor characterization of this learner's NormPair coordinate: policy equality, one-step preservation, and arbitrary finite-iterate preservation are all proved for the concrete learner.

References:
- https://doi.org/10.1016/S0004-3702(02)00376-4
- https://ojs.aaai.org/index.php/AAAI/article/view/5075

## What survives as a serious contribution candidate

### A. A formal non-implication result across domains

The strongest candidate is not a positive equilibrium theorem. It is the explicit proof boundary:

exact learner laws -> factor/representation invariance

does not entail

convergence -> fixed point -> market clearing -> supporting price -> Walrasian existence.

The theorem monolith contains both closed positive learner/factor results and closed countermodels/impossibility statements that prevent these economic conclusions from being promoted without their own hypotheses.

This is stronger than merely saying in prose that assumptions are needed. The formal artifact makes the missing obligations part of the theorem topology.

Novelty status: CANDIDATE ONLY. The dedicated literature review must determine whether an equivalent mechanically auditable cross-domain dependency boundary already exists.

### B. A concrete quotient/factor characterization of the canonical learner

For the canonical learner, NormPair-related states have the same policy, the canonical transition preserves the relation, and arbitrary finite iterates preserve it. This yields a quotient/factor interpretation of the learner dynamics.

The mathematical pattern is established in abstraction and bisimulation literature. The possible contribution is the exact characterization and proof for this learner, not the invention of quotient stability itself.

Novelty status: CANDIDATE ONLY.

### C. A typed dependency topology connecting learning to production/equilibrium theory

The graph distinguishes:

production primitives -> feasible firm plans -> profit-optimal supply;
supply + demand + resources -> aggregate resource balance -> market clearing;
separation/fixed-point machinery -> derived/supporting price;
price + clearing + optimization -> generalized Walrasian equilibrium;
classical structural assumptions -> Arrow–Debreu existence;
equilibrium + local nonsatiation/demand conditions -> Pareto optimality;
Pareto optimality + separate supportability assumptions -> Second Welfare route.

This is not a new economic theorem. The potential contribution is the explicit typed topology that prevents one theorem family from being mistaken for another.

Novelty status: CANDIDATE ONLY.

## Production-side strict-unconditional boundary

For the strict unconditional production surface, use the following formulation:

The Agda development provides a closed semantic contract for competitive production-equilibrium ingredients and a closed countermodel showing that the generalized carrier alone does not entail an equilibrium witness.

That is deliberately weaker than Econlib's exists_equilibrium_prod. Econlib's production existence route supplies substantive regularity, irreducibility, ownership/value, optimization, and market-clearing machinery. The Agda boundary should therefore be presented as an explicit separation between the carrier and the classical existence route—not as a competing existence theorem.

## What should be removed from the thesis novelty section

Remove:

- machine-checked economics as the primary novelty;
- Agda as a novelty claim;
- formalization of Walrasian equilibrium as a novelty claim;
- a new production-side Walrasian existence theorem;
- a new First Welfare or Second Welfare theorem;
- factor stability as a newly invented mathematical concept.

These are either already represented in existing formal/economic literature or are standard mathematical constructions.

## What the thesis can plausibly claim

The thesis can plausibly claim a contribution at the intersection of four layers:

1. A specific exact learner whose invariance and factor structure are characterized rather than assumed.
2. A formal boundary theorem showing that those learner-side results do not supply independent economic convergence/equilibrium premises.
3. A production/equilibrium interface whose terminology and obligations are aligned with established general-equilibrium formalization.
4. A theorem/e-graph topology that makes positive implications, missing premises, and counterexamples simultaneously inspectable.

The key phrase is therefore **formal characterization of the dependency boundary**, not **formalization itself**.

## Adviser-facing contribution statement

The thesis does not claim novelty from formal verification, Agda, or re-proving classical Walrasian results. Its substantive contribution is a mechanically auditable dependency topology for a specific coupled learner/economic system. The formalization characterizes the learner-side invariance and quotient structure that actually follow from the model, while explicitly blocking convergence, fixed-point, market-clearing, supporting-price, and equilibrium-existence conclusions unless their independent economic hypotheses are supplied. On the production side, the interface is aligned with standard competitive-production/Walrasian vocabulary while remaining a semantic contract rather than an unconditional existence theorem. The resulting research contribution is the explicit characterization of what the coupled model entails, what it cannot entail, and where classical economic assumptions enter.

## Required final novelty test

Before the thesis states that this boundary is novel, compare it directly against:

- formal general-equilibrium libraries, especially Econlib and earlier theorem-prover developments;
- learning-in-games literature connecting adaptive dynamics to equilibrium and convergence;
- state abstraction, bisimulation, quotient, and congruence literature for dynamical decision systems;
- formal proof-graph, dependency-graph, e-graph, and theorem-discovery work;
- prior work combining learning dynamics with general-equilibrium or production-economy structure.

If prior work already contains the same boundary, downgrade the claim to an integration/application contribution. If it does not, identify precisely which cross-domain construction is absent and make that the thesis novelty claim.

## Import and Dhall synchronization

No Agda imports are changed. The existing Dhall CI surface compiles both monoliths under the same Agda environment:

`--safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

`--safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

The learner remains the canonical component source and the theorem monolith remains the economic/composition source. The dependency direction is learner -> theorem monolith, not the reverse.

## Verification

The PR head was subsequently verified by GitHub Actions run 1245 (Nix connected composition verification) with conclusion success.

## Finite-candidate price kernel: contribution boundary

The finite-candidate price kernel should be framed as an engineering/formal-methods closure rather than as a new economic existence theorem. It demonstrates that a finite candidate set plus an explicit proof-relevant decision procedure can be exhaustively classified into a supporting candidate or complete rejection certificates.

The result is useful for the thesis only insofar as it makes the dependency boundary executable and proof-relevant. It must not be presented as a replacement for classical supporting-price derivation or Walrasian existence.
