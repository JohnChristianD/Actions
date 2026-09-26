# GRU fractal limit convergence adapter — 2026-09-26

This change adds GRUFractalLimitConvergenceWitness as the smallest carrier-polymorphic adapter between an explicitly supplied convergence predicate and the existing arbitrary-limit GRU closure modules.

The witness contains:
- an approximation sequence indexed by Nat;
- a rank-to-level map and an explicit equation connecting the sequence to finite encodings;
- a supplied Converges predicate and convergence witness;
- an explicit approximation relation;
- the existing coherent finite/limit decoder contract;
- finite decoder left-inverse witnesses.

The derived path is:

supplied convergence witness + coherent decoder + finite left inverse
→ limit-surviving left inverse
→ limit separation
→ arbitrary-limit injectivity.

The convergence predicate remains abstract. This module does not define a topology, prove convergence, infer compactness, or manufacture a limit carrier.

## Boundary

The existing StationaryLimitTheorem has the same deliberate architecture: Converges is a supplied predicate, and stationarity is derived only after convergence and limit preservation are supplied. The new GRU adapter reuses that repository design rather than introducing a second convergence theory.

The limit-injectivity conclusion is obtained from the surviving left inverse, not from convergence alone. This preserves the repository's existing boundary that finite injectivity does not by itself imply injectivity of an arbitrary limit representation.

## Novel composition seam

The new adapter closes the missing interface between the convergence frontier and the GRU limit-closure kernel. It does not close the analytic convergence problem itself.

The remaining obligation for a concrete theorem is therefore an actual inhabitant of GRUFractalLimitConvergenceWitness, including a real limit carrier and a real convergence witness.