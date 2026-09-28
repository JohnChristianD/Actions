# E-graph frontier: MARL physics ↔ generalized Walrasian convergence and injectivity — 2026-09-28

This note is the next semantic e-graph frontier after certified e-graph path composition. It connects the existing MARL/Hodge-Maxwell representation surface with the existing conditional generalized-Walrasian convergence route and the existing global-square injectivity route, without collapsing those obligations into an unconditional equilibrium theorem.

## Semantic graph

The intended dependency topology is:

```text
MARL learner laws
  -> Hodge-Maxwell representation
  -> explicit physics -> learner step conjugacy
  -> n-step / prefix transport
  -> economic update representation
  -> convergence witness
  -> fixed-point witness
  -> generalized Walrasian equilibrium existence

Hodge-Maxwell StateIsomorphism
  -> global encoder injectivity
  -> economic/global-square injectivity

economic primitives
  -> demand + competitive supply
  -> aggregate balance + market clearing
  -> economic update operator
  -> [FRONTIER] convergence from economic assumptions
  -> [CONDITIONAL] fixed-point existence from convergence
  -> [CONDITIONAL] generalized Walrasian existence from fixed point
```

The two branches are intentionally orthogonal. Representation injectivity identifies states through the representation map; it does not imply convergence. Convergence can yield a fixed point only through an explicit convergence/fixed-point interface; a fixed point becomes a generalized Walrasian equilibrium only through the explicit economic closure interface.

## Existing proof-bearing edges

The current repository already contains these proof surfaces:

- `ConnectedContinuousHodgeMaxwellGRURepresentationTheorem` packages a carrier-polymorphic Hodge-Maxwell representation, including inverse structure and global encoder injectivity.
- `CanonicalLearnerHodgeMaxwellCompositionTheorem` supplies the learner/solution representation seam and one-step conjugacy.
- `globalConjugacyEquivalence-iterate` supplies the reusable n-step commuting-square induction kernel.
- `topologicalConvergenceWitness-from-finite-rank-stability` transports an eventual exact finite-rank stabilization witness into the explicit convergence-witness interface.
- `FixedPointExistenceFromConvergence` and `fixedPoint-from-convergence` form the convergence-to-fixed-point bridge.
- `GeneralizedWalrasianFixedPointClosure` and `generalizedWalrasianExistence-from-topological-fixed-point` form the explicit fixed-point-to-economic-existence bridge.
- `megaWalrasianGlobalSquareConjugacy` and `megaWalrasianGlobalSquare-injective` are the existing global-square/injectivity surface.
- `gruf4EconomicInjectivityFromGlobalSquare` is the graph-discovered economic injectivity composition.

These edges are not being reinterpreted as stronger theorems. The Agda term remains the authority; the e-graph records typed dependency evidence.

## Implemented composition seam

The Agda monolith now contains a proof-relevant `EGraphEconomicComposition` record. Its fields are deliberately narrow:

1. an `EGraphSemanticPath` for semantic equality;
2. an explicit convergence-plus-stationarity witness for the economic update;
3. an explicit generalized-Walrasian equilibrium witness at the fixed state;
4. a continuous left-inverse representation witness;
5. the existing A* plan `Monoid` laws;
6. the existing Haskell-like `RawMonad` search surfaces.

The derived `eGraphEconomicComposition-closure` theorem exposes the products independently: semantic equality, eventual convergence, stationarity, generalized-Walrasian equilibrium, and representation injectivity. `eGraphEconomicComposition-injective` is derived only from representation reconstruction.

This is a composition theorem, not a new unconditional equilibrium-existence theorem. The convergence witness and stationarity law are inputs, and the generalized-Walrasian equilibrium witness is also an input. The code therefore does not claim that arbitrary MARL dynamics converge, that a fixed point exists from representation injectivity alone, or that learner stability implies market clearing.

The monad and monoid surfaces remain algebra/search infrastructure. The Agda standard library's `RawMonad` intentionally does not encode the monad laws, so the repository does not promote the raw monad surface into semantic equality or economic validity. citeturn1search0

## MARL physics boundary

The physics branch is similarly conditional. Current work proves representation/conjugacy structure, not a new universal physics law. The missing promotion edge is still the explicit Law-I/Law-III/physics-to-learner witness assembly described in the MARL research note. Once those witnesses inhabit the existing `GlobalConjugacyEquivalence` interface, the already-proved iterate kernel can transport the one-step square to arbitrary horizons.

This is useful for the economic graph because it gives a clean seam:

```text
physics
  -> learner representation
  -> economic-state representation
  -> economic dynamics
```

The last edge requires an explicit economic adapter. It cannot be inferred from Hodge-Maxwell conjugacy alone.

## Literature cross-check

Current literature supports treating these as separate mathematical questions rather than one automatic implication. A 2026 NBER paper on tâtonnement and price setting explicitly studies when equilibrium is stable, while older work gives convergence under specific market assumptions such as gross substitutability. citeturn1search0

Recent MARL theory likewise distinguishes equilibrium concepts from convergence of decentralized learning dynamics: a 2026 paper studies Markov Bayes coarse correlated equilibrium and derives convergence of empirical distributions under explicit regret/evaluation assumptions rather than treating arbitrary MARL as automatically convergent. citeturn1academia12

There is also existing work applying MARL to dynamic general-equilibrium models and validating learned approximate equilibria, but that is an empirical/computational result under a specified model, not a proof that arbitrary MARL dynamics converge to a Walrasian equilibrium. citeturn1academia13

## E-graph status vocabulary

```text
PROVED
  actual Agda derivation is present and typechecked.

CONDITIONAL
  derivation is valid after explicit witness/hypothesis inputs.

FRONTIER
  dependency is identified but the required derivation is absent.

BLOCKED-BY-COUNTEREXAMPLE
  an existing counterexample prevents promotion without stronger assumptions.
```

For this frontier:

- MARL representation → iterate conjugacy: PROVED through the generic conjugacy kernel, conditional on the representation witness.
- Hodge-Maxwell representation → global injectivity: PROVED through the existing inverse-law surface.
- finite-rank stabilization → convergence witness: PROVED as a generic transport theorem.
- convergence → fixed point: CONDITIONAL on the explicit convergence witness.
- fixed point → generalized Walrasian existence: CONDITIONAL on the economic closure witness.
- economic primitives → convergence: FRONTIER.
- learner/physics representation → economic update operator: FRONTIER until an explicit economic adapter is inhabited.
- explicit economic update + supplied convergence/stationarity + supplied equilibrium + supplied representation: PROVED as the new typed composition closure.

## E-graph design rule

The next code-level e-graph abstraction should compose existing proof-bearing edges rather than introduce a second semantic authority. In particular, the semantic seam should remain:

```text
certified theorem/edge
  -> typed path composition
  -> semantic equality / transported witness
```

A* may prioritize the route, but its cost or heuristic is never a proof of convergence, injectivity, fixed-point existence, market clearing, or Walrasian equilibrium.

Knowledge delta:

- `Exotic/ERL/FullCoupled/TheoremsMonolith.agda`: adds the typed economic e-graph convergence/fixed-point/Walrasian/representation composition kernel and derived closure/injectivity/equality theorems.
- `.ci/actions_ci.dhall`: gates the new economic composition symbols in the theorem lane.
- `docs/research/egraph-marl-walrasian-convergence-injectivity-2026-09-28.md`: records the implemented seam, its explicit inputs, and the remaining frontier.
- `README.md`: indexes the research frontier.
- No semantic theorem is promoted merely by documentation; the new closure remains conditional on explicit economic witnesses.
