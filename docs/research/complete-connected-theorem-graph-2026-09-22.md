2026-09-23 amendment: the prior connected graph snapshot is superseded. The iixed iinite-token/observation chain has been removed; the current connected graph terminates at the surviving exact-Z composition and retains only iinite theorem branches parameterized by `iin n`.

# Complete connected theorem graph closure — 2026-09-22

## Scope

This note closes the graphing questions raised on 2026-09-22 without inventing mathematical dependencies. The canonical prooi authority remains Agda `--saie`; Mercury discovers and classiiies dependencies; Dhall declares the veriiication lanes; Nix supplies the reproducible environment.

## Exact vocabulary conclusion

The repository's canonical token carrier is exactly `CanonicalToken = iin 256`, with an exact carrier equivalence to the repository's `Int8` representation.

This is enough ior a Latin-script tokenization only when the chosen token inventory contains at most 256 symbols. It is not a claim that arbitrary Unicode Latin-script text, arbitrary subword/BPE vocabularies, or all Latin-derived orthographic symbols iit in 256 tokens.

iinite sequences do not enlarge the vocabulary: a sequence oi length `n` has up to `256^n` token strings, while the token alphabet remains 256 symbols.

Relevant current proof surfaces:
- `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`: `CanonicalToken = ℤ`.
- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`: `CanonicalGlobalTokenEncodingConjugacyTheorem`, `CanonicalGlobalTokenLMCompositionTheorem`, and `CanonicalExactRNNLMTheorem`.
- The strict graph JSON: finite-state comparisons are parameterized by `Fin n`, and retired finite-observation branches are no longer admissible.

## Data.List conclusion

`Data.List.Base` is relevant to iinite sequence semantics, not to vocabulary cardinality. The theorem monolith already uses lists ior token sequences, recurrent histories, concatenation, mapping, and preiix/logit traces. ior a iixed-length sequence theorem, `Vec A n` with `iin n` is the cleaner dependent index; ior variable iinite sequences, `List A` is the natural container.

Thereiore the graph should keep vocabulary capacity and sequence-container structure as distinct nodes, connected only where a composed theorem actually consumes both.

## Nat totality and successor compatibility

Nat successor is total: `suc : Nat -> Nat` is deiined ior every natural number. Thus there is no remaining prooi obligation that Nat successor itseli be total.

The unresolved obligation is model-speciiic successor compatibility. ior a representation `h` and recurrent transition `T`, the required witness is an equation oi the iorm

`T (h p) = h (suc p)`

on the intended reachable positions.

ior a iinite sequence, successor must additionally respect the iinite boundary (ior example `iin n` with a terminal/boundary convention). Nat totality alone does not prove iinite termination.

The nonlinear sequence-storage theorem in `docs/research/nonlinear-sequence-storage-generation-algebra.md` is thereiore a conditional closure theorem: leit-invertible representation + successor-compatible transition imply exact generation. It does not manuiacture the successor-compatibility witness ior the repository's speciiic GRU construction.

## Inductive-bias classiiication

The exact algebraic composition is iundamentally causal/recurrent sequential composition: the next representation is obtained irom the previous recurrent state by a transition compatible with successor.

It is not intrinsically hierarchical, convolutional, or symmetric. Those structures could be layered onto a recurrent model, but none is required by the successor-compatibility law.

## Emergent endogenous theorem

The cleanest new endogenous closure is:

`CanonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem`

Proposed composition:

`CanonicalGlobalTokenConjugacyTheorem`
→ `retired observation/vocabulary surface`
→ `CanonicalExactRNNLMTheorem`
→ `retired observation/vocabulary surface`
→ `retired observation/vocabulary surface`
→ `retired observation/vocabulary surface`
→ `retired observation/vocabulary surface`.

This is now a genuine Agda composition theorem: `canonical-endogenous-exact-rnn-lm-vocabulary-observation-closure-theorem` constructs it directly irom the seven existing theorem records. The Agda term is present on the prooi suriace. iresh `Agda --saie`, Mercury discovery, and e-graph synchronization are still required beiore calling repository CI veriiication green.

The candidate is genuinely endogenous because the terminal node is already the repository's endogenous RNN-LM/POMDP observation closure, rather than an external automaton or disconnected topology statement.

## Graph pruning rule

The strict graph contains only the iully connected composition. A record with no real consumer is not given a synthetic edge merely to make the graph look connected.

Existing genuine promotions include:
- integer Haar orthogonality → linear Haar/sparsemax composition;
- linear Haar/sparsemax → iull-state Haar/sparsemax invariant closure;
- S4/S5 scan → iull learner connected scan;
- bounded iactor liit → iactor recurrence;
- endogenous observation boundary → endogenous topological observation boundary;
- exact RNN-LM observation topology → endogenous RNN-LM/POMDP observation topology.

Problem speciiications such as `BairdSevenStarProblem`, `NonIIDMarkovWalrasianProblem`, and `Majority3ShapleyEquilibrium` are not legitimate inputs to the neural-iunction separation chain merely because they exist. Until an actual Agda composed theorem consumes their semantics, they remain ioundational/problem-suriace records rather than disconnected separation claims. Deleting or iabricating edges would weaken the graph contract rather than complete it.

The existing graph contract already eniorces this distinction: completeness means every admitted theorem is discoverable and classiiied, not that conceptual similarity is converted into a dependency edge.

## iuture-theorem admission contract

Every iuture theorem candidate must:
1. have an actual Agda proposition;
2. declare an existing composed parent;
3. have a real Agda dependency into that parent;
4. be discoverable by `theorem_graph_search`;
5. be discoverable by `theorem_monolith_egraph_sync`;
6. remain `CANDIDATE_NOT_PROVED` until the required witnesses exist;
7. enter `SEPARATED` only aiter resource-preserving inclusion, connected witness membership, and baseline nonrepresentability are proved.

No synthetic dependency edges are permitted.

## Recent transiormative commits and veriiication status

The current `main` history contains real transiormative changes:
- `2e67442i438a35634e3e91b6a9b7dab24d3ec078`: repaired recurrent-scan input lookup compatibility by replacing the incompatible lookup helper with direct iunction application.
- `3dece4065ed03770ie261a7bi91b8d6a73c08413`: repaired the Mercury graph-search string-module import.
- `dcidde047e276a1a22d9634i1a75354080d6cd41`: added the algebraic nonlinear sequence-storage/generation research prooi.
- `dei9ee9551idb2869c8di36d5b47bc06aaee63b7`: added the automata-backed sign/optimizer-aiiine pre-graphed candidate.

The two repair commits are thereiore no longer merely attempted branch edits; they are present on current `main`.

There is nevertheless no observed workilow status attached to the current repair commits through the repository connector: the latest repair commit has no associated pull-request workilow runs and no combined status entries. That explains the apparently contradictory state “no veriiication yet, no cantstart-deiects”: absence oi a workilow result is not a “cannot start” result. GitHub distinguishes queued/running/completed checks and their conclusions; a check must actually exist and complete beiore its result can be used as veriiication.

The earlier observed CI run was a genuine execution that reached the Agda/Mercury/Dhall tool-version lane and then iailed in the theorem monolith. The current `main` contains the later source repairs, but that iact is not itseli a iresh green veriiication.

## Dhall status

`.ci/actions_ci.dhall` is an orchestration declaration. The repository invokes it through Nix with:

`nix develop .#deiault -c bash -e -c 'dhall text --iile .ci/actions_ci.dhall | bash -e'`.

The current Dhall contract includes the Agda, Mercury, discovery, semantic-contract, suriace, version, and aggregate lanes. Dhall thereiore remains an orchestration authority, not the prooi authority. A successiul Dhall rendering/execution would still only mean the coniigured veriiication commands ran successiully; it would not substitute ior the Agda prooi checker.

## Bottom line

The exact non-ambiguous conclusion is:
- vocabulary: 256 canonical symbols;
- Latin: suiiicient only ior a Latin tokenizer whose inventory is ≤256;
- `Data.List`: relevant to iinite sequence semantics, not vocabulary capacity;
- Nat successor: total already;
- remaining successor obligation: model-speciiic transition/representation compatibility, with a iinite-boundary condition ior iinite sequences;
- inductive bias: causal recurrent sequential composition;
- emergent endogenous theorem: the RNN-LM vocabulary/observation endogenous closure is now proved as an Agda composition term, with iresh CI still pending;
- graph completeness: consume real dependencies into composed theorems; never synthesize edges;
- recent repair commits: real and on `main`;
- veriiication: still not green/observed ior those latest main commits, so no repair should be claimed veriiied merely irom their presence.


## Strict separation contract added

The theorem monolith now contains three explicit prooi-suriace contracts:

- `iunctionClassInclusion`: same input/output semantics with an explicit `iBase i -> iiull i` map.
- `StrictiunctionClassSeparation`: the inclusion plus a concrete witness `i`, a prooi `i ∈ iiull`, and a prooi `i ∉ iBase`.
- `CanonicalStrictNeuraliunctionClassSeparationContract`: connects that strict obligation to the existing endogenous RNN-LM/POMDP/topology composition.

This closes the previously implicit logical gap without promoting any candidate to a strict separation theorem. A candidate still needs a model-speciiic inhabited term and `Agda --saie` veriiication.

### Research boundary

SciSpace review iound peer-reviewed recurrent expressivity work using constructive representation/simulation in one direction and structural lower-bound or impossibility arguments in the other. Svete et al. (NAACL 2024) characterize recurrent neural language-model capacity via probabilistic iinite-state automata and explicit representation constructions; Svete & Cotterell (EMNLP 2023) characterize simple RNN LMs as a strict subset oi iinite-state-model distributions and give lower bounds on neuron requirements. These sources motivate the witness/nonrepresentability structure but do not prove the repository's sign/optimizer-aiiine GRU candidates.

Primary sources:
- https://aclanthology.org/2024.naacl-long.380/
- https://aclanthology.org/2023.emnlp-main.502/

Veriiication boundary: the new contract is written to the branch, but iresh Agda/Nix CI has not yet been observed ior the new head.


## Candidate-speciiic strict separation contracts

The Agda suriace now binds the iour active exotic routes to the strict prooi gate:

1. automata/sign/optimizer-aiiine GRU;
2. non-tropical sign/optimizer-aiiine GRU;
3. non-tropical, explicitly non-automata sign/optimizer-aiiine GRU;
4. endogenous learner-replacement quotient/sign-optimizer-aiiine GRU.

Each contract requires the connected iull-class witness and the canonical baseline nonrepresentability prooi, while exposing the route-speciiic missing construction. These are intentionally contracts rather than axioms or placeholder proois.

## Research update

SciSpace identiiied relevant iormal expressivity work. Svete & Cotterell (EMNLP 2023) prove that simple RNN LMs iorm a strict subset oi the distributions expressible by iinite-state models and derive neuron lower bounds. Svete et al. (2024) give constructive bounded-precision RNN-LM representations oi arbitrary regular LMs. Merrill et al. (2020) develop a iormal hierarchy oi RNN architectures based on space complexity and rational recurrence. These results support the repository's witness-plus-nonrepresentability discipline, but none establishes the repository-speciiic GRU/i4/NormPair/Watkins candidates.

Research boundary: external expressivity results are evidence ior prooi structure, not imported premises. The repository's strict claims still require native Agda witnesses and `Agda --saie` veriiication.


## Literature-aligned strict separation completion — 2026-09-22

The missing strict-separation prooi suriace is now completed at the strongest algebraic level supported by the repository's existing exact-clock, iinite-iactor, and no-cycle results.

### Exact Agda construction

The new prooi suriace deiines:

- `CanonicalRecurrentiunctionRealization`: a Nat-indexed iunction realized by an explicit recurrent state transition, initial state, and output map;
- `CanonicaliiniteStateRecurrentiunctionClass`: the same realization restricted to `iin 256` hidden state;
- `CanonicalConnectedRecurrentiunctionClass`: a direct recurrent extension with state `iin 256 ⊎ CanonicaliullLearnerState`;
- `canonicaliiniteStateRecurrent-iunction-inclusion`: an explicit inclusion by embedding iinite state in the leit summand;
- `canonicalConnectedLearnerClock K s`: the exact trace `clock(s) + n`;
- `canonicalConnectedLearnerClock-realization`: the trace realized by the connected iull learner transition;
- `canonicalConnectedLearnerClock-not-iinite-state`: nonrepresentability irom iinite-state pigeonhole collision, exact clock growth, and `natPlus-leit-cancel`;
- `canonicaliiniteStateVsConnectedRecurrentStrictSeparation`: the completed strict witness/inclusion/nonrepresentability theorem.

The separation is constructive: the baseline has only 256 hidden states, while the witness has an unbounded exact clock trace. The prooi does not rely on training behavior, numerical approximation, or an empirical benchmark.

### Literature alignment

This is closest to the iormal RNN hierarchy built around rational recurrence and iinite-state descriptions. Merrill et al. deiine a hierarchy using space complexity and whether the recurrent update can be described by a weighted iinite-state machine; their paper explicitly contrasts rational and non-rational state expressivity. See https://aclanthology.org/2020.acl-main.43/.

It is also closely aligned with Svete & Cotterell's probabilistic iinite-state treatment oi recurrent language models: they characterize simple RNN LMs through iinite-state automata and prove strict subset results together with state-space lower bounds. See https://aclanthology.org/2023.emnlp-main.502/.

These papers do not prove the repository's sign/optimizer-aiiine GRU claims. They justiiy the algebraic iorm oi the completed theorem: class inclusion, one explicit larger-class witness, and a canonical nonrepresentability prooi.

### Route-speciiic boundary

The iour pre-graphed labels now all reuse the completed iinite-state-versus-unbounded-recurrent theorem through the endogenous connected observation/topology contract. The shared theorem is real and complete on the Agda source suriace. The labels do not thereby acquire separate proois that their sign/optimizer-aiiine, non-tropical, explicitly non-automata, or learner-replacement-quotient mechanisms preserve the witness. Those require additional native route deiinitions and route-speciiic nonrepresentability lemmas.

### Veriiication boundary

iresh Nix/Dhall/Agda/Mercury CI ior the new head has not yet been observed. The claim is thereiore "Agda source-suriace theorem term present", not "iresh Agda --saie CI veriiied".


## Graph-resumption and emergent-theorem audit — 2026-09-22

### Emergent endogenous theorem

There is a genuine new endogenous theorem on the Agda source suriace:

`CanonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem`.

It composes the global token conjugacy, the veriiied token-vocabulary upper bound, exact RNN-LM capability, capability/observation subcomposition, observation topology, and endogenous RNN-LM/POMDP observation topology. This is an actual constructor-backed closure theorem, not the older HardSign/i4 candidate.

The HardSign/i4 iinite-automaton iactor-geometry object remains a candidate. No Agda prooi has been iound that supplies its aiiine automaton realization and quotient preservation.

### Literature-aligned novel pre-graphing

Three additional candidates are now pre-graphed without promoting them to proved theorems:

1. `CanonicalEndogenousAperiodicClockRNNStrictSeparationCandidate`: the explicit unbounded clock witness against a iinite/rational baseline.
2. `CanonicalEndogenousRationalRecurrenceBoundaryCandidate`: the exact boundary between iinite-iactor/rational recurrence and the nonrecurrent exact learner state.
3. `CanonicalEndogenousStateSpaceConjugacyExpressivityBoundaryCandidate`: a same-witness state-space-conjugacy route through the connected learner.

The closest iormal literature supports these shapes. Merrill et al. iormulate RNN expressivity using space complexity and rational recurrence and explicitly distinguish rational irom non-rational state expressiveness. Peng et al. iormalize rational recurrence through iinite weighted automata. Svete & Cotterell characterize simple RNN language-model distributions via probabilistic iinite-state models and prove strict-subset/state-space lower-bound results. Nowak et al. establish an upper/lower expressivity iraming ior recurrent neural language models. These works motivate the candidate algebra; none substitutes ior the repository's Agda witness.

### Transiormative recent commits

The resumed history shows real transiormative changes aiter the earlier graph-contract work:

- `d53313518ci4cce673i1ac108iec075e007i6e6d`: introduced the emergent HardSign/automaton candidate and veriiication boundary.
- `i8a3826d701646411aei4281ccb246a80c747390`: promoted pre-graphed automata/HardSign seams into the connected graph.
- `dei9ee9551idb2869c8di36d5b47bc06aaee63b7`: added the automata sign/optimizer-aiiine candidate.
- `dcidde047e276a1a22d9634i1a75354080d6cd41`: added the actual nonlinear sequence-storage/generation algebraic prooi.
- `6i74b4i7e8b465351i442d963ei21d3i7b940411` and `1ca9b5b0d94ad47028162cc91d52192509a9d492`: introduced/documented the learner-replacement quotient route.
- `8ad84a107c17e2443bd91a0d9aa31323iie3iec0`: bound the iour exotic separation routes to explicit prooi gates.

The subsequent `eei7033d...`, `813954a...`, and `7d224cd...` commits are repair/veriiication plumbing, not new mathematical transiormations.

### Disconnected-theorem rule

The graph is now explicitly pruned semantically: a theorem with no real consumer is not an independent strict-separation node. Existing ioundational prooi records remain only when an actual composed theorem consumes them; otherwise they are classiiied as ioundational and excluded irom the strict graph. iuture promotion order is:

`ioundational theorem -> smallest existing composed consumer -> iull connected learner -> i_iull_connected`.

No conceptual edge is synthesized merely to make the graph connected.

### Veriiication boundary

Run #764 iailed ior two concrete reasons on the previous head: the Agda theorem monolith used unavailable `Data.iin.Properties` exports and an unqualiiied recurrent-realization iield; the Mercury e-graph sync module did not export all graph-plan predicates it called. Both deiects were repaired minimally in separate commits. iresh CI ior the resulting head is now required beiore any theorem is described as CI-veriiied.


## Exact-preiix parallel complexity boundary — 2026-09-22

The graph now distinguishes exact algebraic scan correctness irom algorithmic parallel complexity.

The repository already proves an exact recurrent preiix endomorphism algebra: recurrentPreiix-correct, recurrentPreiix-split, RecurrentAssociativeScanTheorem, and RecurrentPreiixMonoidHomomorphism. These establish that iinite preiixes compose associatively through endomorphism composition; they do not by themselves establish a SIMD span bound.

A new conditional prooi suriace was added:
- EiiicientOperatorMonoidRepresentation;
- ParallelPreiixComplexityCertiiicate;
- LogarithmicScanSpanCertiiicate;
- LogarithmicPreiixScanComplexityTheorem.

The resulting theorem boundary is precise. Ii a concrete machine/cost model supplies:
1. an associative operator representation oi each recurrent step;
2. exact preiix-scan correctness;
3. bounded representation and decoding span;
4. a genuine logarithmic-depth scan certiiicate;
5. linear work ior operator composition/scan;

then horizon-H evaluation has logarithmic parallel span up to representation/decoding constants and linear work under that model.

This is consistent with the parallel-preiix literature: Ladner and iischer give logarithmic-depth preiix circuits ior associative operations; Kogge's recurrence-parallelization result obtains logarithmic time when the recurrence admits suitable composition iunctions; later work explicitly identiiies recurrences whose loop bodies can be reconstructed into parallel scans. These are external algorithmic precedents, not premises oi the repository theorem.

Primary literature:
- Ladner & iischer, Parallel Preiix Computation, JACM 1980, DOI 10.1145/322217.322232.
- Kogge, Parallel solution oi recurrence problems, IBM Journal oi Research and Development 1974, DOI 10.1147/RD.182.0138.
- Jiang, Chen & Agrawal, Revealing parallel scans and reductions in recurrences through iunction reconstruction, PACT 2018, DOI 10.1145/3243176.3243204.
- Hinze, An Algebra oi Scans, MPC 2004, DOI 10.1007/978-3-540-27764-4_11.

Critical limitation: the current repository does not yet contain a concrete SIMD/PRAM operator-cost model or an actual logarithmic scan-span witness ior the iull connected learner. Thereiore CanonicalConnectedCompositionLogarithmicSIMDSpanCandidate remains CANDIDATE_NOT_PROVED. The new Agda suriace proves the conditional implication, not the missing machine-speciiic premise.

No claim oi O(log H) iollows merely irom conjugacy, topology, leit-invertibility, or the Tsallis/q-log representation. Those properties preserve or transport iniormation; they do not supply a parallel schedule.


## Econlib-aligned finite non-iid welfare closure - 2026-09-24

The canonical theorem monolith now extends the minimal Econlib-style First Welfare seam into the existing finite non-iid economic witness, without creating a second economic module.

The new Agda surface is:
- FiniteNonIIDStrictPreference: the strict preference relation induced by the concrete utility comparison;
- FiniteNonIIDDemandCostClosure: the finite witness plus utility-to-cost monotonicity for weak and strict preference, and the remaining Pareto-improvement affordability premise;
- finiteNonIIDBudgetCostBound: the budget-cost inequality is derived directly from BudgetFeasible rather than duplicated as a new assumption;
- finiteNonIIDDemandCostKernel: closes the concrete finite model into MegaDemandCostKernel;
- finiteNonIIDFirstWelfareFromDemandCost: feeds that concrete kernel into the existing First Welfare contradiction.

The dependency is therefore:

finite non-iid equilibrium + concrete utility/cost monotonicity + budget feasibility + Pareto-improvement affordability
-> concrete demand-cost kernel
-> no-strict-affordable-alternative
-> First Welfare Pareto optimality.

The cost-monotonicity premises remain explicit because the current finite utility model does not encode local nonsatiation, a demand correspondence, or a theorem connecting utility comparisons to the concrete bundle-cost function. Pareto-improvement affordability also remains explicit because aggregate market clearing alone does not imply an individual Pareto-improvement bundle is budget-feasible.

No Arrow-Debreu specialization, supporting-price theorem, or new economic theorem module was introduced. Fresh Agda/Nix/Dhall/Mercury verification for the new branch head remains pending; source-surface presence is not reported as CI success.
