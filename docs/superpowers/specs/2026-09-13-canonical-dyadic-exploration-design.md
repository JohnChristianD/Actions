# Canonical Dyadic Exploration Design

## Goal
Make one finite triangular dyadic law the sole stochastic exploration distribution and kernel-check the finite support, normalization, zero-mass, mutation self-loop, and lattice-reachability obligations without claiming unsupported generation-chain theorems.

## Canonical law
`D_tri(k) = (16 - |k|) / 256` for `k ∈ {-15,…,15}`. The implementation represents the 31 support values as integer offsets with weights `1,…,16,…,1`; the total weight is 256.

## Scope
`D_tri` is the only exploration law used by Noisy Nets, OpenES, and MR15-GA. Histogram fitness remains an empirical statistic, not a second sampling distribution. Deterministic Rademacher masks in Fastfood and deterministic RoPE factors remain deterministic.

## Proof boundary
Kernel proofs establish normalization, symmetry, zero mass, Int8 compatibility, exact sampling weights, single-coordinate support steps, a positive-probability self-loop, and reachability of the finite coordinate lattice through the `±1` support witnesses. The full generation-map irreducibility theorem is only stated once its complete finite transition relation (selection, averaging, step adaptation, inner state, and tape state) is represented; no theorem is accepted merely from mutation irreducibility.

## Aperiodicity boundary
A positive-probability support self-loop is proved for the finite mutation kernel. A full joint-chain aperiodicity theorem additionally requires a joint self-loop in the complete transition relation and will not be inferred from subsystem facts alone.

## Arithmetic boundary
All probabilities are natural-number weights over total weight 256; no floating-point or irrational constants are introduced. The implementation never represents literal `1/5`; the MR15 adaptation comparison remains an integer comparison.
