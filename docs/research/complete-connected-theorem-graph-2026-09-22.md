# Complete connected theorem graph closure — 2026-09-22

## Scope

This note closes the graphing questions raised on 2026-09-22 without inventing mathematical dependencies. The canonical proof authority remains Agda `--safe`; Mercury discovers and classifies dependencies; Dhall declares the verification lanes; Nix supplies the reproducible environment.

## Exact vocabulary conclusion

The repository's canonical token carrier is exactly `CanonicalToken = Fin 256`, with an exact carrier equivalence to the repository's `Int8` representation.

This is enough for a Latin-script tokenization only when the chosen token inventory contains at most 256 symbols. It is not a claim that arbitrary Unicode Latin-script text, arbitrary subword/BPE vocabularies, or all Latin-derived orthographic symbols fit in 256 tokens.

Finite sequences do not enlarge the vocabulary: a sequence of length `n` has up to `256^n` token strings, while the token alphabet remains 256 symbols.

Relevant proof surfaces:
- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`: `CanonicalToken = Fin 256`.
- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`: `CanonicalTokenVocabularyUpperBoundTheorem` and global token conjugacy.
- `README.md`: exact vocabulary-capacity statement.

## Data.List conclusion

`Data.List.Base` is relevant to finite sequence semantics, not to vocabulary cardinality. The theorem monolith already uses lists for token sequences, recurrent histories, concatenation, mapping, and prefix/logit traces. For a fixed-length sequence theorem, `Vec A n` with `Fin n` is the cleaner dependent index; for variable finite sequences, `List A` is the natural container.

Therefore the graph should keep vocabulary capacity and sequence-container structure as distinct nodes, connected only where a composed theorem actually consumes both.

## Nat totality and successor compatibility

Nat successor is total: `suc : Nat -> Nat` is defined for every natural number. Thus there is no remaining proof obligation that Nat successor itself be total.

The unresolved obligation is model-specific successor compatibility. For a representation `h` and recurrent transition `T`, the required witness is an equation of the form

`T (h p) = h (suc p)`

on the intended reachable positions.

For a finite sequence, successor must additionally respect the finite boundary (for example `Fin n` with a terminal/boundary convention). Nat totality alone does not prove finite termination.

The nonlinear sequence-storage theorem in `docs/research/nonlinear-sequence-storage-generation-algebra.md` is therefore a conditional closure theorem: left-invertible representation + successor-compatible transition imply exact generation. It does not manufacture the successor-compatibility witness for the repository's specific GRU construction.

## Inductive-bias classification

The exact algebraic composition is fundamentally causal/recurrent sequential composition: the next representation is obtained from the previous recurrent state by a transition compatible with successor.

It is not intrinsically hierarchical, convolutional, or symmetric. Those structures could be layered onto a recurrent model, but none is required by the successor-compatibility law.

## Emergent endogenous theorem

The cleanest new endogenous closure is:

`CanonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem`

Proposed composition:

`CanonicalGlobalTokenConjugacyTheorem`
→ `CanonicalTokenVocabularyUpperBoundTheorem`
→ `CanonicalExactRNNLMTheorem`
→ `CanonicalExactRNNLMCapabilitySubcompositionTheorem`
→ `CanonicalExactRNNLMObservationSubcompositionTheorem`
→ `CanonicalExactRNNLMObservationTopologyCapabilityTheorem`
→ `CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem`.

This is now a genuine Agda composition theorem: `canonical-endogenous-exact-rnn-lm-vocabulary-observation-closure-theorem` constructs it directly from the seven existing theorem records. The Agda term is present on the proof surface. Fresh `Agda --safe`, Mercury discovery, and e-graph synchronization are still required before calling repository CI verification green.

The candidate is genuinely endogenous because the terminal node is already the repository's endogenous RNN-LM/POMDP observation closure, rather than an external automaton or disconnected topology statement.

## Graph pruning rule

The strict graph contains only the fully connected composition. A record with no real consumer is not given a synthetic edge merely to make the graph look connected.

Existing genuine promotions include:
- integer Haar orthogonality → linear Haar/sparsemax composition;
- linear Haar/sparsemax → full-state Haar/sparsemax invariant closure;
- S4/S5 scan → full learner connected scan;
- bounded factor lift → factor recurrence;
- endogenous observation boundary → endogenous topological observation boundary;
- exact RNN-LM observation topology → endogenous RNN-LM/POMDP observation topology.

Problem specifications such as `BairdSevenStarProblem`, `NonIIDMarkovWalrasianProblem`, and `Majority3ShapleyEquilibrium` are not legitimate inputs to the neural-function separation chain merely because they exist. Until an actual Agda composed theorem consumes their semantics, they remain foundational/problem-surface records rather than disconnected separation claims. Deleting or fabricating edges would weaken the graph contract rather than complete it.

The existing graph contract already enforces this distinction: completeness means every admitted theorem is discoverable and classified, not that conceptual similarity is converted into a dependency edge.

## Future-theorem admission contract

Every future theorem candidate must:
1. have an actual Agda proposition;
2. declare an existing composed parent;
3. have a real Agda dependency into that parent;
4. be discoverable by `theorem_graph_search`;
5. be discoverable by `theorem_monolith_egraph_sync`;
6. remain `CANDIDATE_NOT_PROVED` until the required witnesses exist;
7. enter `SEPARATED` only after resource-preserving inclusion, connected witness membership, and baseline nonrepresentability are proved.

No synthetic dependency edges are permitted.

## Recent transformative commits and verification status

The current `main` history contains real transformative changes:
- `2e67442f438a35634e3e91b6a9b7dab24d3ec078`: repaired recurrent-scan input lookup compatibility by replacing the incompatible lookup helper with direct function application.
- `3dece4065ed03770fe261a7bf91b8d6a73c08413`: repaired the Mercury graph-search string-module import.
- `dcfdde047e276a1a22d9634f1a75354080d6cd41`: added the algebraic nonlinear sequence-storage/generation research proof.
- `def9ee9551fdb2869c8df36d5b47bc06aaee63b7`: added the automata-backed sign/optimizer-affine pre-graphed candidate.

The two repair commits are therefore no longer merely attempted branch edits; they are present on current `main`.

There is nevertheless no observed workflow status attached to the current repair commits through the repository connector: the latest repair commit has no associated pull-request workflow runs and no combined status entries. That explains the apparently contradictory state “no verification yet, no cantstart-defects”: absence of a workflow result is not a “cannot start” result. GitHub distinguishes queued/running/completed checks and their conclusions; a check must actually exist and complete before its result can be used as verification.

The earlier observed CI run was a genuine execution that reached the Agda/Mercury/Dhall tool-version lane and then failed in the theorem monolith. The current `main` contains the later source repairs, but that fact is not itself a fresh green verification.

## Dhall status

`.ci/actions_ci.dhall` is an orchestration declaration. The repository invokes it through Nix with:

`nix develop .#default -c bash -e -c 'dhall text --file .ci/actions_ci.dhall | bash -e'`.

The current Dhall contract includes the Agda, Mercury, discovery, semantic-contract, surface, version, and aggregate lanes. Dhall therefore remains an orchestration authority, not the proof authority. A successful Dhall rendering/execution would still only mean the configured verification commands ran successfully; it would not substitute for the Agda proof checker.

## Bottom line

The exact non-ambiguous conclusion is:
- vocabulary: 256 canonical symbols;
- Latin: sufficient only for a Latin tokenizer whose inventory is ≤256;
- `Data.List`: relevant to finite sequence semantics, not vocabulary capacity;
- Nat successor: total already;
- remaining successor obligation: model-specific transition/representation compatibility, with a finite-boundary condition for finite sequences;
- inductive bias: causal recurrent sequential composition;
- emergent endogenous theorem: the RNN-LM vocabulary/observation endogenous closure is now proved as an Agda composition term, with fresh CI still pending;
- graph completeness: consume real dependencies into composed theorems; never synthesize edges;
- recent repair commits: real and on `main`;
- verification: still not green/observed for those latest main commits, so no repair should be claimed verified merely from their presence.


## Strict separation contract added

The theorem monolith now contains three explicit proof-surface contracts:

- `FunctionClassInclusion`: same input/output semantics with an explicit `FBase f -> FFull f` map.
- `StrictFunctionClassSeparation`: the inclusion plus a concrete witness `f`, a proof `f ∈ FFull`, and a proof `f ∉ FBase`.
- `CanonicalStrictNeuralFunctionClassSeparationContract`: connects that strict obligation to the existing endogenous RNN-LM/POMDP/topology composition.

This closes the previously implicit logical gap without promoting any candidate to a strict separation theorem. A candidate still needs a model-specific inhabited term and `Agda --safe` verification.

### Research boundary

SciSpace review found peer-reviewed recurrent expressivity work using constructive representation/simulation in one direction and structural lower-bound or impossibility arguments in the other. Svete et al. (NAACL 2024) characterize recurrent neural language-model capacity via probabilistic finite-state automata and explicit representation constructions; Svete & Cotterell (EMNLP 2023) characterize simple RNN LMs as a strict subset of finite-state-model distributions and give lower bounds on neuron requirements. These sources motivate the witness/nonrepresentability structure but do not prove the repository's sign/optimizer-affine GRU candidates.

Primary sources:
- https://aclanthology.org/2024.naacl-long.380/
- https://aclanthology.org/2023.emnlp-main.502/

Verification boundary: the new contract is written to the branch, but fresh Agda/Nix CI has not yet been observed for the new head.


## Candidate-specific strict separation contracts

The Agda surface now binds the four active exotic routes to the strict proof gate:

1. automata/sign/optimizer-affine GRU;
2. non-tropical sign/optimizer-affine GRU;
3. non-tropical, explicitly non-automata sign/optimizer-affine GRU;
4. endogenous learner-replacement quotient/sign-optimizer-affine GRU.

Each contract requires the connected full-class witness and the canonical baseline nonrepresentability proof, while exposing the route-specific missing construction. These are intentionally contracts rather than axioms or placeholder proofs.

## Research update

SciSpace identified relevant formal expressivity work. Svete & Cotterell (EMNLP 2023) prove that simple RNN LMs form a strict subset of the distributions expressible by finite-state models and derive neuron lower bounds. Svete et al. (2024) give constructive bounded-precision RNN-LM representations of arbitrary regular LMs. Merrill et al. (2020) develop a formal hierarchy of RNN architectures based on space complexity and rational recurrence. These results support the repository's witness-plus-nonrepresentability discipline, but none establishes the repository-specific GRU/F4/NormPair/Watkins candidates.

Research boundary: external expressivity results are evidence for proof structure, not imported premises. The repository's strict claims still require native Agda witnesses and `Agda --safe` verification.


## Literature-aligned strict separation completion — 2026-09-22

The missing strict-separation proof surface is now completed at the strongest algebraic level supported by the repository's existing exact-clock, finite-factor, and no-cycle results.

### Exact Agda construction

The new proof surface defines:

- `CanonicalRecurrentFunctionRealization`: a Nat-indexed function realized by an explicit recurrent state transition, initial state, and output map;
- `CanonicalFiniteStateRecurrentFunctionClass`: the same realization restricted to `Fin 256` hidden state;
- `CanonicalConnectedRecurrentFunctionClass`: a direct recurrent extension with state `Fin 256 ⊎ CanonicalFullLearnerState`;
- `canonicalFiniteStateRecurrent-function-inclusion`: an explicit inclusion by embedding finite state in the left summand;
- `canonicalConnectedLearnerClock K s`: the exact trace `clock(s) + n`;
- `canonicalConnectedLearnerClock-realization`: the trace realized by the connected full learner transition;
- `canonicalConnectedLearnerClock-not-finite-state`: nonrepresentability from finite-state pigeonhole collision, exact clock growth, and `natPlus-left-cancel`;
- `canonicalFiniteStateVsConnectedRecurrentStrictSeparation`: the completed strict witness/inclusion/nonrepresentability theorem.

The separation is constructive: the baseline has only 256 hidden states, while the witness has an unbounded exact clock trace. The proof does not rely on training behavior, numerical approximation, or an empirical benchmark.

### Literature alignment

This is closest to the formal RNN hierarchy built around rational recurrence and finite-state descriptions. Merrill et al. define a hierarchy using space complexity and whether the recurrent update can be described by a weighted finite-state machine; their paper explicitly contrasts rational and non-rational state expressivity. See https://aclanthology.org/2020.acl-main.43/.

It is also closely aligned with Svete & Cotterell's probabilistic finite-state treatment of recurrent language models: they characterize simple RNN LMs through finite-state automata and prove strict subset results together with state-space lower bounds. See https://aclanthology.org/2023.emnlp-main.502/.

These papers do not prove the repository's sign/optimizer-affine GRU claims. They justify the algebraic form of the completed theorem: class inclusion, one explicit larger-class witness, and a canonical nonrepresentability proof.

### Route-specific boundary

The four pre-graphed labels now all reuse the completed finite-state-versus-unbounded-recurrent theorem through the endogenous connected observation/topology contract. The shared theorem is real and complete on the Agda source surface. The labels do not thereby acquire separate proofs that their sign/optimizer-affine, non-tropical, explicitly non-automata, or learner-replacement-quotient mechanisms preserve the witness. Those require additional native route definitions and route-specific nonrepresentability lemmas.

### Verification boundary

Fresh Nix/Dhall/Agda/Mercury CI for the new head has not yet been observed. The claim is therefore "Agda source-surface theorem term present", not "fresh Agda --safe CI verified".


## Graph-resumption and emergent-theorem audit — 2026-09-22

### Emergent endogenous theorem

There is a genuine new endogenous theorem on the Agda source surface:

`CanonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem`.

It composes the global token conjugacy, the verified token-vocabulary upper bound, exact RNN-LM capability, capability/observation subcomposition, observation topology, and endogenous RNN-LM/POMDP observation topology. This is an actual constructor-backed closure theorem, not the older HardSign/F4 candidate.

The HardSign/F4 finite-automaton factor-geometry object remains a candidate. No Agda proof has been found that supplies its affine automaton realization and quotient preservation.

### Literature-aligned novel pre-graphing

Three additional candidates are now pre-graphed without promoting them to proved theorems:

1. `CanonicalEndogenousAperiodicClockRNNStrictSeparationCandidate`: the explicit unbounded clock witness against a finite/rational baseline.
2. `CanonicalEndogenousRationalRecurrenceBoundaryCandidate`: the exact boundary between finite-factor/rational recurrence and the nonrecurrent exact learner state.
3. `CanonicalEndogenousStateSpaceConjugacyExpressivityBoundaryCandidate`: a same-witness state-space-conjugacy route through the connected learner.

The closest formal literature supports these shapes. Merrill et al. formulate RNN expressivity using space complexity and rational recurrence and explicitly distinguish rational from non-rational state expressiveness. Peng et al. formalize rational recurrence through finite weighted automata. Svete & Cotterell characterize simple RNN language-model distributions via probabilistic finite-state models and prove strict-subset/state-space lower-bound results. Nowak et al. establish an upper/lower expressivity framing for recurrent neural language models. These works motivate the candidate algebra; none substitutes for the repository's Agda witness.

### Transformative recent commits

The resumed history shows real transformative changes after the earlier graph-contract work:

- `d53313518cf4cce673f1ac108fec075e007f6e6d`: introduced the emergent HardSign/automaton candidate and verification boundary.
- `f8a3826d701646411aef4281ccb246a80c747390`: promoted pre-graphed automata/HardSign seams into the connected graph.
- `def9ee9551fdb2869c8df36d5b47bc06aaee63b7`: added the automata sign/optimizer-affine candidate.
- `dcfdde047e276a1a22d9634f1a75354080d6cd41`: added the actual nonlinear sequence-storage/generation algebraic proof.
- `6f74b4f7e8b465351f442d963ef21d3f7b940411` and `1ca9b5b0d94ad47028162cc91d52192509a9d492`: introduced/documented the learner-replacement quotient route.
- `8ad84a107c17e2443bd91a0d9aa31323ffe3fec0`: bound the four exotic separation routes to explicit proof gates.

The subsequent `eef7033d...`, `813954a...`, and `7d224cd...` commits are repair/verification plumbing, not new mathematical transformations.

### Disconnected-theorem rule

The graph is now explicitly pruned semantically: a theorem with no real consumer is not an independent strict-separation node. Existing foundational proof records remain only when an actual composed theorem consumes them; otherwise they are classified as foundational and excluded from the strict graph. Future promotion order is:

`foundational theorem -> smallest existing composed consumer -> full connected learner -> F_full_connected`.

No conceptual edge is synthesized merely to make the graph connected.

### Verification boundary

Run #764 failed for two concrete reasons on the previous head: the Agda theorem monolith used unavailable `Data.Fin.Properties` exports and an unqualified recurrent-realization field; the Mercury e-graph sync module did not export all graph-plan predicates it called. Both defects were repaired minimally in separate commits. Fresh CI for the resulting head is now required before any theorem is described as CI-verified.
