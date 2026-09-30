{
  date = "2026-09-30",
  scope = "External SMT assistance, safe Agda proof boundary, Vehicle interoperability boundary, and graph verification",
  request = "Install Schmitty for automated SMT assistance and assess whether Vehicle or its emergent compositions belong in the theorem/graph stack.",
  affected_code = [
    ".ci/actions_ci.dhall",
    ".github/workflows/nix-composition.yml",
    "flake.nix",
    "Exotic/ERL/FullCoupled/TheoremsMonolith.agda",
    "ProofAutomation/SchmittyAssisted.agda",
    "README.md",
    "docs/research/agda-smt-vehicle-boundary-2026-09-30.md"
  ],
  knowledge_delta = [
    ".ci/change-record-2026-09-30-schmitty-vehicle-smt.dhall",
    "docs/research/agda-smt-vehicle-boundary-2026-09-30.md"
  ],
  changes = [
    "Added a dedicated Schmitty/Z3 CI lane using a Schmitty-compatible Agda toolchain with --allow-exec, without importing Schmitty into the --safe proof authority.",
    "Added a safe Schmitty boundary record whose witness is the existing IntegerRingSolver theorem, preserving a single mathematical authority.",
    "Added Z3 to the pinned Nix development shell for local SMT tooling.",
    "Removed the stale JSONJSON heredoc terminator from the shared Pages Dhall lane.",
    "Recorded Vehicle as an explicit future interoperability boundary because its current Agda library targets standard-library 2.3 while the repository proof environment uses standard-library 2.4.",
    "Kept the Mercury graph theorem source unchanged as an Agda-safe monolith consumer; the new automation is not promoted as a new nonredundant domain theorem."
  ],
  verification = [
    "Schmitty source and test shape were checked against upstream v1.0.1 before integration.",
    "The pinned nixpkgs package set was checked and does not provide the Schmitty Agda library or the Vehicle Agda backend; the workflow therefore installs Schmitty through setup-agda and does not add an unverified Vehicle derivation.",
    "The Vehicle Agda formalisation boundary remains separate because its current Agda library targets a different standard-library line; no Vehicle theorem is promoted into the canonical proof graph.",
    "The Schmitty lane isolates external SMT execution under Agda --allow-exec and never changes the --safe proof-authority monoliths.",
    "A minimal --allow-exec probe showed the failure occurs while source-checking safe standard-library modules; the first bootstrap wrote interfaces under setup-agda's installed library tree but Agda still rechecked source files.",
    "The previous production lane was contradictory: it first compiled the Schmitty dependency tree with --safe and then requested --allow-exec, which Agda rejects because --allow-exec is incompatible with --safe.",
    "The remediation copies the pinned Schmitty dependency sources to runner temp and executes only the non-safe Schmitty witness; the canonical safe mirror remains in TheoremsMonolith.agda.",
    "The next verification receipt on the current head is authoritative for the corrected Schmitty witness and the unchanged graph lanes."
  ],
  caveat = "Schmitty/Z3 is external execution evidence, not Agda --safe proof authority. Vehicle-derived statements are not admitted into the proof graph until a version-compatible translation layer exists.",
  stale_when = "Update this record when the Schmitty/Z3 setup, canonical Agda/std-lib versions, Vehicle Agda dependency, or theorem-graph authority changes."
