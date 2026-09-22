# Actions — Exact Recurrent Learner, RNN-LM, and Theorem-Graph Monograph

This repository develops a small, exact formal system for recurrent learning, sequence models, finite observation boundaries, optimizer composition, and theorem discovery. The canonical executable learner and canonical theorem surface are intentionally separated: Agda is the proof authority, Mercury performs semantic extraction and graph search, Dhall declares the CI lanes, and Nix supplies reproducible composition.

The central methodological rule is simple: exact statements remain exact. A graph candidate is not promoted merely because its name sounds plausible; its dependency path must be exposed and its Agda statement must type-check. The repository therefore treats theorem discovery as a search problem over already-declared semantic laws, with A*-style cost guidance and e-graph equality saturation used as discovery/extraction machinery rather than as a replacement for proof.

## CORL / continual and online learning perspective

The formal learner is a recurrent state machine with explicit state, recurrent scans, policy readout, and optimizer state. This makes continual/online-learning questions concrete: what information is retained, which transformations are policy-invariant, which observations lose information, and which exact compositions remain transportable?

The strongest conclusions are structural rather than empirical. The canonical state evolution has exact clock growth and excludes nontrivial finite cycles. Exact finite-state observations can recur even when the full state does not. A global exact left inverse from the finite observation carrier is therefore blocked on the unbounded exact orbit.

## Informatics and formal semantics

The repository treats recurrent prefixes as algebraic objects. A recurrent prefix induces an endomorphism; list concatenation is translated into composition under the chosen execution convention; componentwise products preserve the same monoid law. Exact state isomorphisms transport equality, disequality, iteration conjugacy, and finite-cycle exclusion.

## Neuromorphic interpretation

The recurrent learner can be read as a discrete event-driven dynamical system with bounded integer carriers and explicit recurrent state. This is a formal analogy, not a hardware claim. The topology layer is a genuine dependency: the endogenous topological observation boundary combines exact scan conjugacy, finite-cycle transport, and the information loss induced by a finite observation carrier.

## Biostatistics and stochastic semantics

Finite probability semantics are represented with exact natural-number weights and a positive total rather than introducing an unnecessary second analytic tower. Finite POMDP probability objects, exact transport, and belief-state update transport form a separate semantic seam.

The stationary theorem surface is deliberately conditional: a stationary-limit theorem records a transition law, a convergence premise, and preservation of the limiting law. It does not smuggle a Lyapunov argument into the development. The MarkovStationary Walrasian material is likewise kept distinct from a general equilibrium-existence claim.

## Mathematical physics

The finite recurrent carrier, exact orbit structure, endomorphism monoids, product composition, and topology/observation boundary provide a discrete dynamical-systems language. The repository does not infer physical laws from the learner; it isolates mathematical structures that also occur in discrete dynamics: trajectories, invariants, recurrence, conjugacy, finite projections, and stationary measures.

A deterministic finite cycle would admit a stationary probability witness on its cycle, but the canonical exact learner separately proves that its own full-state evolution has no nontrivial finite cycle. Stationarity and recurrence are therefore kept logically distinct.

## Theoretical computer science

The strongest computational boundary is exact rather than asymptotic. The canonical learner has a finite Int8 state carrier while its exact clock is unbounded. This yields pigeonhole obstructions to globally injective finite-state representations of the unbounded orbit and rules out the repository's specified exact one-step two-counter simulation contract.

That statement is intentionally narrower than a universal claim about every possible notion of Turing completeness.

## RNN-LM capability surface

The canonical token carrier has exact encode/decode inverses with Int8. The exact RNN-LM theorem, global token conjugacy, token prefix monoid law, logit-trace append law, shared sparsemax policy/weight surfaces, and architecture-preserving RNN-LM isomorphism are represented as formal capabilities rather than performance claims.

The theorem graph now pre-graphs an exact RNN-LM observation/topology capability closure:

Exact RNN-LM → token conjugacy → architecture-preserving transport → endogenous observation → endogenous topology → finite-information boundary.

Two lower-level RNN-LM subcompositions remain visible so graph search can choose their paths independently. They are promotion candidates until Agda --safe and the Mercury graph type-check them.

The vocabulary result is similarly exact. CanonicalTokenVocabularyUpperBoundTheorem states an exact finite-carrier boundary for the canonical token alphabet. It is not a claim about the vocabulary size of arbitrary real-world language models.

## nLab / category-theory / philosophy of structure

The category-theoretic reading is intentionally modest. State representations behave like objects connected by isomorphisms; recurrent transitions behave like endomorphisms; exact conjugacy transports dynamical properties; recurrent prefixes form an action of a free monoid on the state space; product constructions lift componentwise actions.

The philosophical lesson is methodological: preserve distinctions between object, representation, observation, and proof. An observation map is not the state itself. A transport theorem is not an existence theorem. A graph path is not a proof until its terminal Agda statement type-checks. An e-graph equality is a candidate semantic identification, not authority over the formal development.

## Monograph architecture

The development is organized around one canonical learner module and one canonical theorem monolith.

- Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda — executable/state semantics.
- Exotic/ERL/FullCoupled/TheoremsMonolith.agda — active exact theorem surface.
- .ci/discovery/theorem_graph_search.m — semantic-law extraction and dependency search.
- .ci/discovery/theorem_monolith_egraph_sync.m — e-graph synchronization and graph gates.
- .ci/actions_ci.dhall — declarative CI orchestration.
- docs/monolith-sync.md — synchronization and promotion notes.

GitHub workflows are intended to run the declared checks on repository events; the workflow graph is an execution artifact, while the Agda theorem graph remains the semantic authority. GitHub documents workflow files under .github/workflows and the visualization graph for workflow dependencies. citeturn0search0turn0search3

## Exactness policy

No theorem is promoted by weakening a gate, replacing a missing proof with a vacuous proposition, or silently changing a carrier to make a composition fit.

- no Lyapunov theorem is required merely to discuss a stationary-limit contract;
- no generic Walrasian existence theorem is fabricated from the concrete MarkovStationary example;
- no sparsemax specialization is treated as an intrinsic dyadic law;
- no F4 contraction theorem is claimed without an actual contraction hypothesis/proof;
- no e-graph extraction is treated as proof authority;
- no RNN-LM capability theorem is interpreted as a benchmark or universal language-model performance claim.

The desired end state is a graph in which the strongest useful exact subcompositions emerge automatically from declared semantic laws, after which selected, type-checked compositions can be promoted into the canonical learner monolith.

## Status and limitations

The repository is a formal development, not empirical validation of a deployed learner. Exact equalities are meaningful relative to the carriers and operations actually formalized. Generalization to continuous probability, infinite vocabularies, unrestricted neural architectures, biological systems, physical systems, or economic environments requires additional formal hypotheses.

The graph-search system is deliberately not an autonomous mathematical oracle. It can discover and rank compositions of declared semantic laws; Agda remains responsible for establishing the actual proposition.

## Citation and contribution

For a contribution, preserve the distinction between semantic declarations, graph candidates, and checked theorem proofs. New mathematical surfaces should first be added to the theorem monolith, then exposed to graph search, then type-checked before promotion.

The README is intentionally a monograph-style map of the current formal vocabulary rather than a replacement for the individual theorem statements.