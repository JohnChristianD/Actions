# Unconditional tragedy-of-the-commons non-derivability — 2026-09-26

## Result

The theorem monolith now contains an explicit interface-level impossibility boundary between individual local optimality and aggregate preservation of a shared resource.

The formal countermodel is deliberately non-vacuous and now carries the depletion quantities explicitly:

- two agents share a resource whose capacity is one unit;
- each agent's individually optimal action extracts one unit;
- the aggregate extraction field is explicitly two units;
- the preservation predicate is the capacity condition `2 ≤ 1`, which is refuted constructively by `twoNotLeOne`.

The theorem interface also exposes `resourceCapacity`, `extraction`, and `aggregateExtraction`, so the concrete witness is no longer just an arbitrary false preservation predicate.

Core result:

    noUnconditionalCommonsPreservation

with the concrete witness:

    twoAgentCommonsCounterexample

The concrete witness therefore models the mechanism rather than making `preserves` an arbitrary empty predicate.

## Interpretation

This is a theorem about derivability from an interface, not a claim that every empirical commons collapses. It establishes that local optimality plus a shared-resource carrier does not, by itself, entail aggregate preservation.

Hence there must not be an unconditional graph edge:

    individual optimality -> commons preservation

Nor does market clearing alone supply the missing conservation mechanism:

    individual optimality + market clearing -X-> commons preservation

A positive theorem must expose additional coupling information.

## Positive routes

A preservation theorem can add, for example:

- an aggregate resource constraint;
- an internalized externality;
- quotas or property rights;
- a regeneration/dynamics law;
- a conservation invariant;
- an explicit coordination condition.

These are assumptions or mechanisms that connect individual actions to aggregate resource state. They are not consequences of local optimality alone.

## Relation to the existing economic graph

The repository's economic topology already separates supply/demand from aggregate resource balance and market clearing. The commons boundary adds a distinct negative edge below the price/equilibrium layer.

The conceptual composition is:

    local optimality
         |
         v
    individual extraction
         |
         v
    shared resource
         |
         v
    aggregate extraction
         |
         X
         v
    commons preservation

while a conditional route is:

    local optimality
         +
    explicit common-resource coupling
         ->
    aggregate conservation
         ->
    sustainable allocation

This keeps the commons non-derivability boundary distinct from canonical-price non-identifiability: the former concerns local-to-global resource preservation; the latter concerns recovering a price from insufficient observations.

## Literature boundary

The formal result should not be read as the universal empirical claim that all common-pool resources are doomed. Elinor Ostrom's Nobel lecture explicitly discusses both overharvesting social dilemmas and cases where users self-organize to manage common-pool resources. The formal contribution here is narrower and compositional: without an explicit coupling mechanism in the theorem interface, preservation is not derivable from local optimality alone.
