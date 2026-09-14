# Dyadic GRU theorem ordering

Agda `--safe` is the acceptance boundary. This document records structural implications only.

Flat dyadic has the strongest law-level symmetry surface because every Int8 point has the same numerator. Therefore every finite relabelling preserves weight, and every state is an immediate support witness. Lazy unit and dyadic ladder retain zero mass, symmetry, a unit generator, and finite dyadic normalization, but their support is smaller.

Law ordering:

flatDyadic >= lazyUnit and flatDyadic >= dyadicLadder

The `>=` relation here means theorem-surface inclusion, not task performance. A strict inequality requires a property possessed by flat and absent from the compared law. Full-support one-step reachability and all-relabeling weight invariance supply such witnesses in the current finite model.

Method ordering is different. MR15-GA, OpenES, and recurrent Noisy Nets are method tags over the same finite coupled state. Their law-level irreducibility, self-loop, and period-one results are therefore inherited uniformly whenever the selected law supplies the corresponding generator and zero witnesses.

Noisy Nets gains a separate recurrent representation theorem through `RecurrentProjection`: projection after lift is exact, and coupled recurrent steps lift representation targets. This is the required bridge before calling recurrent exploration stronger than a gate-only theorem.

The recurrent theorem class adds:

- three explicit recurrent matrices;
- finite dyadic gate substitutions;
- finite signReLU candidate substitution;
- global optimizer and global L2 carried through the recurrent state;
- Mobius endomorphism composition;
- associative scan equivalence at operator level;
- sparsemax/Haar/Walsh-Rademacher finite representation composition;
- finite DPG actor/critic transport with critic max-bootstrap relation.

A strict Noisy Net dominance theorem over MR15 or OpenES still needs a method-state simulation whose image is preserved by the recurrent transition. The current projection/lift theorem proves the representation bridge, not a universal method simulation. The safe conclusion is therefore a strict structural extension of the theorem surface, not a total ordering of methods.

Sparsemax should remain a finite projection node in the canonical proof surface. If it is learned, its parameters use the same global optimizer and L2 carrier. If it is frozen, it contributes no learned state. The present finite theorem surface keeps the projection node deterministic.

The recurrent scan is compatible with structured semiseparable reasoning only at the algebraic operator level: a Mobius endomorphism composes associatively, so a balanced scan can reproduce the sequential composition. This establishes an associative-scan theorem without claiming a separate matrix-factorization theorem.
