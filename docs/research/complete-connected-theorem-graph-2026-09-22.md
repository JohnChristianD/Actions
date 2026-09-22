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
