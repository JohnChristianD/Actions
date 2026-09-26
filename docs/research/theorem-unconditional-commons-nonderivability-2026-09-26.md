# Unconditional tragedy-of-the-commons non-derivability — 2026-09-26

## Result

The theorem monolith now contains an explicit interface-level impossibility boundary between individual local optimality and aggregate preservation of a shared resource.

The new theorem says that, for a countermodel carrying:

- a shared resource;
- locally optimal actions for every agent; and
- failure of the aggregate preservation predicate;

there is no unconditional derivation from universal local optimality to preservation.

Core result:

    noUnconditionalCommonsPreservation

with the concrete witness:

    twoAgentCommonsCounterexample

## Interpretation

This is intentionally stronger as a composition boundary than a claim about a particular empirical commons. It says that the semantic interface does not contain enough information to manufacture an aggregate sustainability conclusion from local optimality alone.

Therefore the graph must not contain an unconditional edge:

    individual optimality -> commons preservation

nor the stronger shortcut:

    individual optimality + market clearing -> commons preservation

unless the missing coupling assumptions are made explicit.

## Positive routes

A positive preservation theorem can instead expose one or more mechanisms such as:

- an aggregate resource constraint;
- an internalized externality;
- quotas or property rights;
- a regeneration/dynamics law;
- a conservation invariant;
- an explicit coordination condition.

Those are conditional bridges, not consequences of local optimality by themselves.

## Relation to the existing economic graph

The repository's economic topology already separates supply/demand from aggregate resource balance and market clearing. This new theorem adds a separate negative edge: market clearing or local optimization cannot silently be promoted into a commons-preservation theorem.

The resulting conceptual graph is:

    local optimality
         |
         X
         v
    commons preservation

while a conditional route is:

    local optimality
         +
    explicit common-resource coupling
         -> aggregate conservation
         -> sustainable allocation

This keeps the tragedy-of-the-commons boundary distinct from the canonical-price non-identifiability boundary: the former is about aggregate resource governance; the latter is about recovering a price from insufficient observations.