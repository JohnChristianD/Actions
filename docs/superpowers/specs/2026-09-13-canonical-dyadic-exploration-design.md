# Canonical Dyadic Exploration Design

## Goal
Make one finite triangular dyadic law the sole stochastic exploration distribution and kernel-check the finite support, normalization, zero-mass, direct lattice moves, and the composed learner+EA aperiodicity boundary without claiming unsupported full-chain irreducibility.

## Canonical law
`D_tri(k) = (16 - |k|) / 256` for `k ∈ {-15,…,15}`. The implementation represents the 31 support values as integer offsets with weights `1,…,16,…,1`; the total weight is 256.

## Canonical exploration mechanism
The canonical outer explorer is the modified MR15-GA finite generation operator. The choice is theorem-driven, not empirical: MR15 exposes a finite population of 16 four-coordinate genomes, an explicit member tape and coordinate tape, top-`N/4` selection, exact coordinatewise mean, integer one-fifth success adaptation, and a neutral no-perturb transition. The canonical finite MR15 layer therefore has 16 × 4 = 64 directly addressable population-coordinate axes. The current Noisy-Net gate has one scalar noise input at `gateWeight`, so its direct stochastic control is one scalar axis. This establishes a formal exploration-control advantage (64 addressable EA axes versus 1 scalar gate-noise axis), not a convergence theorem.

The Noisy-Net gate also preserves the diagonal subspace definitionally: equal pair inputs remain equal after the common scalar gate weight. That is an exact finite-state limitation of the current implementation. MR15 instead applies an explicitly chosen coordinate and noise value to each offspring through its finite mutation tapes.

## Modified MR15 generation
The canonical generation state is finite: population of 16 genomes over 4 coordinates in `Fin 256`, a mean genome, an exponent in `Fin 15`, and a success count in `Fin 17`. Each perturbing generation deterministically ranks the 16 population members, keeps the top 4, updates the mean by exact integer division, adapts the exponent using the integer comparison `5 * successes <= 16`, and mutates one selected coordinate of each offspring using a D_tri noise value repeated `2^exponent` times. The no-perturb gate is an explicit neutral transition and is part of the finite transition relation.

## Scope
D_tri is the sole stochastic exploration law used by the canonical MR15 operator. Histogram statistics, robust fitness summaries, deterministic Rademacher masks, and deterministic RoPE factors are not second sampling distributions. Legacy Noisy-Net/OpenES/MR15 skeleton modules outside the canonical path are comparison/history only.

## Proof boundary
Kernel-checkable layers now include: the actual finite D_tri support; a complete finite MR15 generation map; the actual `CanonicalLearner.step`; the actual composed learner+EA transition; separate genome-lattice, EA-generation, and full-coupled reachability relations; and a generic full-state aperiodicity theorem. The older repository MR15 mutation relation already has a formal invariant obstruction to full population irreducibility, so the new canonical MR15 layer does not inherit an unsupported global-reachability claim.

Full generation-map irreducibility is accepted only when its complete transition relation, including learner state and all EA state, has an inhabitant of the explicit irreducibility obligation. The current code has not earned that inhabitant yet.

## Aperiodicity boundary
A D_tri neutral support value alone does not imply full-chain aperiodicity. The canonical composed transition has an explicit full-state self-loop at `startCoupled`. The generic Agda theorem proves that this self-loop plus full composed-state irreducibility yields two consecutive positive return lengths at every state, hence the standard period-1 criterion, without using causality or online/replay equivalence.

## Arithmetic boundary
All sampling probabilities are natural-number weights over total weight 256; no floating-point or irrational constants are introduced. The MR15 adaptation uses the exact integer comparison `5 * successes <= 16` and never represents literal `1/5`.
