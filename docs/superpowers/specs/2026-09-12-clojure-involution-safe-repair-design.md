# Clojure local involution discovery for safe Agda repair

## Purpose

Use Clojure as a pure discovery/composition layer for local, self-inverse transformations while preserving Agda `--safe` as the authoritative theorem gate.

## Design

The Clojure layer has no mutable global state and no dependency on the Agda proof state. Local transformations are ordinary functions over finite vectors. `adjacent-swap` and `sign-flip` are involutions; disjoint composition is checked by finite extensional testing.

Repair selection is deliberately narrower than the basis search. It uses a finite allowlist keyed by an exact Agda error marker and source precondition. Each rewrite is idempotent: applying the same rule twice produces byte-identical source.

The repair layer must never edit `.ci/external/efficient-chad-agda`, weaken a theorem, delete a proof obligation, or bypass `agda --safe`. An unknown error selects `:none` rather than guessing.

## Verification

The Clojure workflow runs on pull requests, main pushes, hourly schedule, and manual dispatch. It executes the Clojure tests and prints the discovered local basis. The existing Agda workflow remains independent and authoritative for kernel closure.

Future repair automation may consume a captured Agda error/source pair and apply only an allowlisted Clojure rule before re-running `agda --safe`; no automatic repair is accepted without the kernel gate turning green.
