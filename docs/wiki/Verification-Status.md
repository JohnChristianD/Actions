# Verification Status

Last audited: 2026-09-19 against `main` at `d48e5cf6e3671f268440135f1acc32eeafb3d510`.

## Current code head

The current `main` ref points at:

`d48e5cf6e3671f268440135f1acc32eeafb3d510`

GitHub's combined status query currently returns no status entries for that commit. Accordingly, this ledger records configuration and source state without labeling the remote run green.

## Active theorem source

The canonical theorem entrypoint remains:

`Exotic/ERL/FullCoupled/TheoremsMonolith.agda`

The canonical learner implementation is:

`Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`

The generalized learner/theorem monoliths remain separate benchmark/general infrastructure.

## Active discovery implementation

The current discovery source set is:

```
.ci/discovery/learner_semantic_extractor.m
.ci/discovery/learner_semantic_manifest.m
.ci/discovery/novel_learner_theorem_discovery.m
.ci/discovery/symbolic_egraph.m
.ci/discovery/symbolic_egraph_test.m
.ci/discovery/interpolated_theorem_egraph.m
.ci/discovery/interpolated_theorem_egraph_test.m
```

The executable semantics are manifest-driven.

The extractor reads:

- `CanonicalLearnerMonolith.agda`
- `TheoremsMonolith.agda`

and derives theorem-like declarations plus source-level dependencies.

The generator then filters composite declarations and writes the generated Agda aliases.

There is no current Mercury-side transformation grammar, observable registry, or symbolic theorem table.

## Current generated artifact

`Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda` is generated with `{-# OPTIONS --safe #-}`.

The current artifact contains four aliases:

```
generatedSemanticDerived0 = canonicalStep-not-fixed
generatedSemanticDerived1 = clockAfter
generatedSemanticDerived2 = canonicalAperiodic
generatedSemanticDerived3 = canonicalNoCountedTwoCycle
```

These are existing theorem declarations projected through the extracted semantic dependency mechanism. They are not automatically merged back into `TheoremsMonolith.agda`.

The JSON report produced by the generator records:

```
symbolic_registry = false
refl_as_composition = false
proof_authority = "Agda --safe"
```

The filename/report term "Novel" is historical. The current source does not perform independent novel-law synthesis.

## Generic e-graph verification

The current Guix driver executes:

```
Mercury semantic discovery
Mercury generic e-graph regression
Mercury interpolated theorem e-graph regression
generated-artifact proof-shape audit
Agda --safe
```

The generic e-graph regression exercises the implementation in `.ci/discovery/symbolic_egraph.m`.

The interpolated theorem e-graph consumes the same extracted semantic manifest. It checks that the generated symbolic graph is nonempty and source-derived. It does not establish learner theorem truth.

There is no current "8 -> 4 candidate quotient" theorem-discovery claim in the executable source. That statement belonged to the retired hand-authored grammar architecture and has been removed from this ledger.

## Agda safe lane

`.guix/ci.scm` regenerates the discovery artifact, audits it for the exact bare string `= refl`, and then runs `agda --safe` over the configured proof/test surface plus the generated module.

Agda `--safe` is used as the proof authority. The relevant property is that safe mode disables postulates, unsafe OPTIONS pragmas, and `primTrustMe`, among other consistency-sensitive features. The repository's own scanner additionally rejects forbidden theorem/axiom markers in the configured proof files.

## Current configuration mismatch

The current `.guix/ci.scm` function `agda-safe-files` still names:

`Exotic/ERL/FullCoupled/CanonicalClosedLoopInterface.agda`

The path is absent from the current `main` tree.

Therefore the configured Agda lane and the current source tree are not perfectly synchronized. This is a concrete CI configuration mismatch, not evidence that the missing module still exists.

The current workflow file itself has four lanes:

- Agda `--safe` connected theorem surface;
- Mercury connected theorem and verifier lane;
- Mercury semantic-discovery lane;
- repository surface audit.

## Surface audit

The Guix `surface` lane rejects repository source files with the retired Haskell, Python, shell-script, JavaScript/TypeScript, JVM-language, Elm, and PureScript suffixes.

This is a repository hygiene gate. It is not a theorem about the learner.

## Legacy discovery removal

The current tree no longer contains the older TSTS/JAxtar Mercury discovery modules or the Mercury oracle described by earlier wiki versions.

The surviving TSTS theorem is an Agda theorem surface, not an active Mercury search target.

## Verification interpretation

The repository distinguishes four claims:

```
source exists
    !=
Mercury generated a file
    !=
Agda accepts the generated proposition
    !=
remote CI status is green
```

The first two are source/configuration facts visible in Git. The third requires an actual Agda run. The fourth requires an observed workflow result.

For the current main head, only the source/configuration facts are directly established here. The remote status API currently exposes no status entries for the head.
