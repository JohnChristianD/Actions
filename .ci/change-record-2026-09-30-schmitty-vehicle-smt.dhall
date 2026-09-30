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
    "The pinned nixpkgs agda package set was checked and does not provide a schmitty package; the CI lane therefore installs Schmitty through the documented Agda library mechanism.",
    "The current Vehicle Agda library metadata was checked and declares standard-library-2.3, so no direct canonical import was added.",
    "The seventh Schmitty attempt reached the end of the shared Dhall source but failed because the top-level merge expression was never applied to lane and the bound script was never returned.",
    "The eighth Schmitty attempt executed the witness path and failed because cda-tum/setup-z3 supplied a binary requiring glibc 2.38+ while Ubuntu 22.04 provides an older glibc.",
    "The ninth Schmitty attempt proved the pinned nixpkgs Z3 path works (Z3 4.16.0) but Agda 2.6.2.2 could not resolve Data.Integer because the installed standard-library and Schmitty libraries were not registered in defaults.",
    "The Schmitty CI setup now mirrors the upstream Schmitty v1.0.1 integration shape: standard-library is selected by agda-stdlib-version, Schmitty is installed as a library, and the witness uses the agda executable on PATH rather than the setup action's agda-exe output. This removes repo-specific setup differences from the non-authoritative SMT lane. No theorem, Vehicle, or graph semantics are changed. Final SMT and graph receipts remain pending."
  ],
  caveat = "Schmitty/Z3 is external execution evidence, not Agda --safe proof authority. Vehicle-derived statements are not admitted into the proof graph until a version-compatible translation layer exists.",
  stale_when = "Update this record when the Schmitty/Z3 setup, canonical Agda/std-lib versions, Vehicle Agda dependency, or theorem-graph authority changes."
