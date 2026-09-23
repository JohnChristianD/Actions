# Hodge-Maxwell/Tsallis/Walrasian projection bridge — 2026-09-23

## Decision

The new proof surface is a conditional, proof-relevant composition:
`ConnectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosureTheorem`.

It consumes:
- `ConnectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem`;
- `ConnectedGeneralizedWalrasianExistenceTheorem`;
- an explicit decoder from Hodge-Maxwell/Tsallis solution states to Walrasian allocations;
- an equilibrium-to-fixed-point compatibility certificate; and
- the reverse fixed-point-to-equilibrium compatibility certificate.

This is a genuine graph dependency because the Agda record fields name and consume the existing theorem records. It does not create a synthetic mathematical edge.

## Boundary

The unbounded `Int8.code : ℤ` upgrade remains a carrier/algebra representation change. It does not establish categorical finite limits, analytic limits, convexity, Fenchel/Legendre duality, differentiability or convexity of a Tsallis q-log, or a regular-economy Walrasian existence theorem.

A finite-carrier impossibility theorem can rule out exact finite encoding of an explicitly unbounded/injective family under its stated premises. That is not the same proposition as “finite limits are impossible.” Finite limits in category theory are a structural existence property and require a category and the relevant limit cones; analytic limits require a topological/metric setting and convergence data.

## Runtime boundary

Dhall remains the repository configuration boundary. Tcl/Lua/Chibi are not required by the Int8 upgrade or by this theorem bridge. They should remain absent unless a concrete future component introduces a demonstrated runtime dependency.

## Graph policy

Zero-dependency theorem-like surfaces are not assigned synthetic edges. A theorem is promoted into the connected graph only when its Agda declaration consumes actual proof-relevant dependencies. Candidate analytic bridges remain candidate-only until the missing certificates exist.

## Verification status

The branch was edited through the GitHub repository interface. Local Agda execution is still unavailable in this environment because outbound network/DNS access is unavailable; no local typecheck result is claimed. CI remains authoritative.
