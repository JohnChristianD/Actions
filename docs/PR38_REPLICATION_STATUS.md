# PR38 replication status

Canonical learner remains a single self-contained Agda source at `Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda`.

Default representation width: `d = 64 = 4^3`.

Direct imports in the canonical learner are exactly:

1. `Relation.Binary.PropositionalEquality`
2. `Agda.Builtin.Nat`
3. `Data.Nat`
4. `Data.Fin`
5. `Data.Fin.Properties`
6. `Data.Nat.DivMod`
7. `Data.Product`
8. `Data.Empty`

The maintained theorem boundary includes:

- sparsemax + LCB policy selection;
- Watkins critic transitions;
- finite negative-Munchausen signed-scale theory;
- learned sparsemax -> Walsh -> GRU factorization and congruence;
- finite Sion saddle-point boundary;
- F4/L2 optimizer and NormPair invariance;
- exact Nat-clock finite-cycle exclusion;
- canonical-policy CartPole closed-loop execution;
- finite return/regret/success benchmark records.

The canonical learner is environment-independent. Game modules remain external test fixtures.

The benchmark records are deterministic finite projections and are not interchangeable with upstream float32/JAX/CleanRL empirical reports. Native action-space claims are made only where the policy head has the required arity.
