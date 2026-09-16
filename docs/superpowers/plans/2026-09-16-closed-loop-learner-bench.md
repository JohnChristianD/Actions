# Closed-Loop Learner Benchmark Implementation Plan

**Goal:** Build a faithful closed-loop learner/environment interface, exact finite return/regret/success records, a ceteris-paribus negative-Munchausen ablation surface, stronger CNN state-transition preservation, and prune redundant learner-era modules while retaining the canonical environment-free learner monolith.

**Architecture:** `CanonicalLearnerMonolith.agda` remains the sole learner dependency and stays environment-agnostic. New interface/benchmark files import that monolith plus the existing game-port module; no game definition is copied into the learner. Multi-action environments use an explicit action-adapter boundary until a genuinely general-A critic is formalized.

**Tech Stack:** Agda 2.8.0, stdlib 2.4, `--safe`, existing eight direct standard-library imports in the canonical monolith.

## Global constraints

- Keep `CanonicalLearnerMonolith.agda` self-contained and environment-free.
- Do not add imports to the canonical learner monolith.
- Game ports remain separate modules.
- No holes, postulates, placeholders, or unverified analytical claims.
- Treat the current two-action canonical sparsemax as two-action until a general-A theorem is actually implemented.
- Record return, reference, regret, success, and steps as exact Nat values.
- Keep external benchmark comparisons descriptive, with metric and environment provenance stated.

## Tasks

1. Closed-loop interface: define a generic finite action/environment interface, exact metrics, canonical two-action actor path, explicit larger-action adapters, and clock/roundtrip proofs.
2. Munchausen ablation: define a numeric finite q-log code, no-Munchausen and sign-flipped variants, ceteris-paribus identities, and a nonzero witness.
3. CNN transition preservation: define encoder/decoder maps, exact representation equivalence, one-step simulation congruence, and iteration closure without universal expressivity claims.
4. Prune redundant learner-era modules after repository-local import closure proves zero users.
5. Synchronize CI, theorem generator, replication wiki, and benchmark reference ledger.
