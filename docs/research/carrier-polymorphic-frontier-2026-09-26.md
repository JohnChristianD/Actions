# Carrier-polymorphic frontier closure — 2026-09-26

This batch makes four boundaries explicit in the formal surface.

## 1. No generic `Fin n` learner/physics carrier

The canonical learner's `Int8` name is not a bounded machine integer in the current source. Its payload is an unbounded `ℤ`. The carrier-polymorphic representation layer remains parameterized by `Set`; `Fin n` is reserved for theorem surfaces whose semantics are genuinely finite.

## 2. Behavior policy is an explicit observable

The canonical learner now exposes:

`BehaviorPolicy = Nat → SparseWeight`

through `canonicalBehaviorPolicy`, while `canonicalPolicy` / `canonicalBehaviorAction` remain the selected-action readout. No probability-normalization or full information-set behavioral-strategy theorem is silently inferred.

## 3. Finite-cycle exclusion does not fundamentally require the clock

The new `StrictProgressWitness` abstraction proves that any strictly increasing, transitive, irreflexive measure excludes every positive finite cycle.

The canonical learner has a clock-free instantiation through its `Nat` `totalCount`, because the exact source already proves:

`totalCount (lcbCounts (canonicalFullStep K s)) = suc (totalCount (lcbCounts s))`.

The mathematical principle is strict progress, not time bookkeeping.

## 4. Law-IV / four-law closure remains witness-gated

The existing `FourLawClosureWitnesses` contract requires an actual Law-I witness, Law-III variational witness, and physics→learner transition-conjugacy witness. The frontier graph therefore treats missing inhabitants as blocking premises rather than manufacturing them.

The economic boundary remains separate:

`learner factor stability → representation/factor information`

does not automatically yield

`convergence → fixed point → market clearing → supporting price → Walrasian existence`.

## External consistency check

The current Econlib `main` repository describes its `Equilibrium` layer as containing Walrasian existence, the first and second welfare theorems, Walras' law, and the Arrow–Debreu production layer. Its design principles emphasize explicit model objects and type-level invariants.

That supports using the same production-side vocabulary in this repository, while keeping the Agda production contract strictly below Econlib's classical existence results until the corresponding assumptions and proofs are actually supplied.

External source checked 2026-09-26:
https://github.com/danlyng/Econlib

This is terminology/semantic alignment, not a claim that the Agda production contract reproduces Econlib's Lean proofs.

## Frontier status taxonomy

- **PROVED** — closed safe-Agda term.
- **CONDITIONAL** — requires an explicit witness or assumption record.
- **FRONTIER** — exact missing bridge identified but not inhabited.
- **BLOCKED** — a closed counterexample or impossibility result prevents unconditional promotion.
- **LITERATURE** — external mathematical/economic result used for boundary comparison.

## Tool roles

Agda remains proof authority. Mercury remains discovery/transport tooling. Mermaid remains the human topology projection. Graph membership is never promoted to proof merely because a path was discovered.
