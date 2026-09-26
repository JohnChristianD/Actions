# Stationary-distribution / finite-cycle obstruction graph

```text
Econlib::FiniteMarkovChain.exists_stationary
        |
        v
  stationary distribution
        |
        | finite deterministic projection required
        v
Agda::finiteOrbit-collision
        |
        v
  periodic orbit exists
        |
        v
Agda::canonicalNoNontrivialFiniteCycle-theorem
        |
        v
  only period-1 / fixed-point recurrence remains
        |
        v
Agda::canonicalNoFiniteStepConvergenceToFixedPoint
        |
        v
  contradiction
```

The obstruction is conditional on an exact finite-state deterministic projection of the canonical orbit. The full canonical learner is not represented as a finite-state Markov chain merely because its cycle-exclusion invariant is Nat-valued; Econlib's finite-state stationary theorem therefore still requires an explicit finite-state projection.

The graph therefore strengthens the finite-cycle exclusion theorem without claiming a nonexistent unconditional stationary-distribution theorem for the full learner.

For the finite-state branch, `finiteOrbit-collision` supplies the pigeonhole recurrence premise. The no-cycle theorem excludes every recurrence of positive period, and the no-fixed-point theorem excludes the remaining period-1 case.

The resulting strict terminal is `IMPOSSIBILITY`, while `FiniteMarkovChain.exists_stationary` remains an independent `EXISTENCE` node.

The Econlib convergence result is stronger under strict positivity: `FiniteMarkovChain.geometric_convergence_to` gives geometric convergence to a supplied stationary law when all transition probabilities are strictly positive.