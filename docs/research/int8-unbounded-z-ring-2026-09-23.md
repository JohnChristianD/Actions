# Unbounded Int8 integer-ring upgrade — 2026-09-23

## Scope

The two small econlib Agda monoliths, `Exotic/econlib/GameTheory.agda` and `Exotic/econlib/Equilibrium.agda`, now keep the public `Int8` name but change its representation from `Fin 256` to Agda's unbounded integer type `ℤ`.

The change is intentionally narrow:

- `Int8.code : ℤ`
- `int8OfNat n = int8 (+ n)`
- finite modulo arithmetic and `Fin 256` imports are removed from these two files
- game scores and equilibrium values use `ℤ), including its order and multiplication
- the existing concrete witnesses remain unchanged numerically

The Agda standard library documents `ℤ) as its integer type, with constructors for non-negative and negative integers, integer ordering, addition, subtraction, and multiplication. Its integer examples also use `+ n` as the natural-to-integer conversion. See the standard-library `Data.Integer.Base` and `README.Data.Integer` documentation.

## Mathematical boundary

This upgrade gives an unbounded integer carrier and ring operations/order available to the affected code. It does **not** prove existence of finite limits in the categorical or analytic sense. Finiteness and completeness are separate structures.

It also does not by itself prove convexity, Fenchel/Legendre duality, a HardSign subgradient theorem, Tsallis q-log differentiability/convexity, or a Hodge-Maxwell/Walrasian bridge. Those require explicit convex-space/barycentric structure, dual pairing/functionals, and the relevant analytic identities. The existing Hodge-Maxwell/Tsallis graph therefore remains conditional at those seams rather than receiving a synthetic edge.

## Graph policy

The integer upgrade is a representation/algebra change, not a new theorem consumer of the strict Hodge-Maxwell graph. No synthetic theorem edge was added merely to make the graph appear connected. Existing theorem records remain the authoritative graph vertices, and future theorem declarations still need a proof-relevant consumer before entering the strict required graph.

The useful next graph seam is therefore an explicit theorem that consumes the new `ℤ)-valued carrier together with independently proved convexity/duality certificates. Until those certificates exist, the bridge remains candidate-only.

## Runtime boundary

Dhall remains the repository's total configuration/embedded scripting layer. Its official documentation states that Dhall is total and not Turing-complete, and that integration with larger systems is performed through language support, external conversion executables, or rendering. Nothing in this Int8 upgrade creates a Tcl, Lua, or Chibi runtime requirement. Those runtimes should remain absent unless a concrete future component demonstrates a real runtime dependency.

## Verification status

The GitHub-hosted environment was used for the branch mutation and file inspection. A local Agda build could not be run in this environment because outbound DNS/network access was unavailable. Therefore this change must not be reported as locally typechecked until CI or another actual Agda invocation verifies it.
