# ZPF ω³ / GRU statistical law boundary — 2026-09-25

## Scope

This note records the repository implementation of the graph's additional ZPF law:

`ZPF -> F_ZPF (homogeneous, isotropic, stochastic Maxwell field) -> omega^3 spectral law`.

The implementation is intentionally a typed semantic boundary. It does not assert that a concrete physical ZPF state or a concrete ZPF-to-GRU encoder exists.

## Primary-source findings

Ibison and Haisch, *Physical Review A* 54, 2737 (1996), describe the classical electromagnetic zero-point field used in stochastic electrodynamics as a homogeneous, isotropic ensemble of plane electromagnetic waves, with stochasticity carried by the wave phases. They also explicitly distinguish the classical ZPF statistics from the quantum vacuum statistics, so the repository should not silently identify the two theories.

Source: https://journals.aps.org/pra/abstract/10.1103/PhysRevA.54.2737

Boyer, *Physical Review D* 11, 790 (1975), formulates random electrodynamics with Maxwell fields plus a Lorentz-invariant classical electromagnetic zero-point-radiation boundary condition and a stochastic radiation field.

Source: https://journals.aps.org/prd/abstract/10.1103/PhysRevD.11.790

A later cavity treatment gives the commonly used angular-frequency spectral-density convention

`rho(omega) = hbar * omega^3 / (2 * pi^2 * c^3)`

and notes the divergence of the idealized density when integrated over an unbounded frequency range. This convention is recorded here as semantic motivation, not as an Agda arithmetic theorem.

Source: https://www.sciencedirect.com/science/article/pii/S1386947705001657

Boyer's 1969 derivation instead describes the zero-point spectrum as linear in frequency **per normal mode**. The distinction demonstrates why the formal interface must keep the spectral-density convention explicit rather than hard-code a bare numerical formula into the arithmetic-free proof layer.

Source: https://journals.aps.org/pr/abstract/10.1103/PhysRev.182.1374

## Repository model

`ZPFOmegaCubedSpectralLaw` records:

- a spectral density for every ZPF state and frequency;
- an explicit frequency multiplication operation;
- a proof that the named `omegaCubed` carrier equals the triple product of the frequency;
- an explicit spectral-density normalization carrier;
- an equality witnessing that the state-dependent density follows that omega-cubed law.

`ZPFMaxwellSemanticData` records the additional semantic predicates for:

- the ZPF field map;
- homogeneity;
- isotropy;
- stochastic semantics;
- Maxwell satisfaction;
- the omega-cubed spectral law.

`ZPFGRUStatisticalRepresentation` then couples those physical semantics to the existing canonical GRU statistical observation through the repository's carrier-polymorphic representation kernel.

## Injectivity result

The module derives global ZPF-state injectivity from the existing theorem

`statisticalEncodeInjective`

using exactly the same decode-after-encode mechanism already used by `GRUStatisticalInjectivity.agda`.

Therefore the formal result is:

`encode z1 == encode z2 -> z1 == z2`

for every ZPF representation whose explicit decoder satisfies

`decode (encode z) == z`.

This is a representation theorem. It does **not** derive the omega-cubed spectrum from injectivity, and it does **not** supply a physical ZPF realization.

## Verification boundary

The new Agda file is intended to be compiled under the repository's existing `--safe` standard-library lane. The repository semantic index and CI file inventory treat it as a surviving FullCoupled module.

The graph status should therefore distinguish:

`ZPF omega^3 law = typed AGDA contract`

from

`concrete ZPF realization = still an external/semantic witness requirement`.

