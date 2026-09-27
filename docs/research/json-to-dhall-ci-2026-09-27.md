# CI artifact format decision — JSON to Dhall — 2026-09-27

## Decision

The repository's structured CI and discovery artifacts use Dhall instead of JSON.

Dhall is already part of the pinned Nix development environment and is already the repository's CI orchestration language. The migration therefore removes a serialization format without adding another runtime, parser, or package.

Tcl is not adopted for this role. The repository has no demonstrated need for a Tcl artifact interpreter, and adding Tcl would introduce a second scripting and serialization model without a corresponding CI requirement.

## Scope

The migration covers committed structured discovery artifacts, runtime theorem/economic/equilibrium/stationarity/transport reports, CI artifact-upload paths, validation checks, and documentation references that treated JSON as the canonical machine-evidence format.

Agda remains the proof authority. Mercury remains the dependency and discovery engine. Dhall carries machine-readable CI evidence and interchange artifacts.

Where JSON previously permitted heterogeneous edge arrays, the Dhall representation uses homogeneous edge records with an optional textual reason field. This keeps the artifact structurally typed rather than relying on untyped array positions.

## Related tooling decisions

Bazel is not added under Dhall. The current workload is repository-local and deterministic, while Nix already owns the reproducible environment and Dhall owns the CI lane declaration. A second build graph and cache layer would add overlap without a demonstrated monorepo build or remote-cache requirement.

HTMX and Rails provide web-application and UI infrastructure, while Dhall-derived graph data remains the machine-readable interchange surface.

## Verification policy

CI rejects tracked JSON files and generated .ci/discovery/*.json artifacts. Generated Dhall reports are parsed with dhall text --file before their semantic field checks.

No theorem semantics are changed by this migration.
