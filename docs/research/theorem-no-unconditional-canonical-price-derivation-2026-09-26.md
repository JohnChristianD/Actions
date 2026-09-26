# Unconditional canonical-price non-derivability — 2026-09-26

## Result

The theorem monolith now distinguishes **price existence** from **price derivation/identification**.

The new countermodel preserves all of the following:

1. At least one equilibrium exists.
2. Every equilibrium is Pareto-optimal.
3. Two worlds are observationally identical after the price-bearing component is forgotten.
4. The two worlds have disjoint supporting-price sets.

Therefore no function from the price-free observation to a supporting price can be sound for both worlds.

The core theorem is:

    not CanonicalPriceDerivation

for the explicit two-world countermodel.

## Why this is stronger than the existing Second Welfare boundary

The existing boundary establishes:

    Pareto(x) does not imply exists p. Equilibrium(p,x)

That countermodel permits the equilibrium set to be empty.

The new boundary instead establishes equilibrium existence together with universal Pareto optimality of equilibria, while still ruling out an unconditional price constructor from the specified observations.

Thus the obstruction is not **non-existence of equilibrium**. It is **non-identifiability of a supporting price from insufficient observables**.

## Formal mechanism

CanonicalPriceDerivation contains:

- derive : Obs -> Price
- a soundness condition requiring derive (observe world) to support every supplied equilibrium allocation in that world.

CanonicalPriceNonIdentifiabilityCounterexample supplies:

- two worlds;
- a common observation;
- an equilibrium witness in each world;
- universal Pareto optimality of equilibria;
- disjoint supporting-price sets.

The generic theorem noUnconditionalCanonicalPriceDerivation feeds the single derived price into both supporting relations and obtains a contradiction from the disjointness condition.

The concrete twoWorldCanonicalPriceNonIdentifiabilityCounterexample uses two prices and two worlds. Each world supports only its corresponding price.

## Economic interpretation

This does **not** say that equilibrium prices cannot exist. An equilibrium witness may contain a price explicitly.

It says that equilibrium existence plus Pareto optimality is insufficient, by itself, to reconstruct a price from a coarser observation that omits the price-bearing economic information.

For classical economic models, additional assumptions can restore positive results: uniqueness after normalization, explicit budget/utility/production structure, convexity, separation, KKT/duality conditions, or another theorem that makes the supporting-price correspondence single-valued or constructively recoverable.

Accordingly, the theorem graph should keep these distinct:

    equilibrium existence -> Pareto optimality
    market clearing + explicit economic assumptions -> supporting price

while rejecting the unconditional shortcut:

    equilibrium existence + Pareto optimality -> canonical price

## Relation to the finite candidate-price kernel

finiteCandidatePriceSearch remains a different result. It can classify a supplied finite candidate list when an explicit decision procedure for the supporting relation is supplied. It does not derive a price from primitive economic observations.

This new theorem closes the conceptual gap by showing that even adding equilibrium existence and universal Pareto optimality does not make unconditional price reconstruction valid.