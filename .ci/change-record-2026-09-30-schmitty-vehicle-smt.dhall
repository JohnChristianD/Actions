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
    "The pinned nixpkgs package set does not provide the Schmitty Agda library or a Vehicle Agda backend; Schmitty is installed through setup-agda and Vehicle remains a separate interoperability boundary.",
    "The Schmitty lane isolates external Z3 execution and never changes the --safe proof-authority monoliths.",
    "Upstream Schmitty v1.0.1 runs its --allow-exec witness through a file-local OPTIONS pragma rather than passing --allow-exec as a command-line flag; this is required because the command-line flag applies globally and conflicts with imported --safe standard-library modules in Agda 2.6.2.2.",
    "The production lane now matches the upstream invocation shape and removes the temporary interface bootstrap.",
    "Graph/proof verification remains independently authoritative; external SMT assistance is non-authoritative evidence only.",
    "The latest CI receipt on the current head is authoritative for the Schmitty witness and the unchanged graph lanes."
  ],  caveat = "Schmitty/Z3 is external execution evidence, not Agda --safe proof authority. Vehicle-derived statements are not admitted into the proof graph until a version-compatible translation layer exists.",
  stale_when = "Update this record when the Schmitty/Z3 setup, canonical Agda/std-lib versions, Vehicle Agda dependency, or theorem-graph authority changes."
