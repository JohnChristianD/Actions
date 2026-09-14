# Dyadic GRU theorem ordering

Agda `--safe` is the acceptance boundary. This document records structural implications only.

The canonical exploration law is flat dyadic. Every Int8 point has the same dyadic numerator weight, so finite relabelling preserves weight and every finite state is an immediate support witness.

Canonical law surface:

flatDyadic

Lazy-unit and dyadic-ladder distributions are retired from the canonical theorem surface. They must not be generated, imported by canonical modules, or used as alternate probability laws.

Method surface is orthogonal to the law. MR15-GA, OpenES, and recurrent Noisy Nets are method tags over the same finite coupled state. Their law-level irreducibility, self-loop, and period-one results are checked against the single flat-dyadic law.

Noisy Nets has a separate recurrent representation theorem through `RecurrentProjection`: projection after lift is exact, and coupled recurrent steps lift representation targets. This is the representation bridge; it is not a universal method-simulation theorem.

The recurrent theorem class contains:

- three explicit recurrent matrices;
- finite dyadic gate substitutions;
- finite signReLU candidate substitution;
- global optimizer and global L2 carried through the recurrent state;
- Mobius endomorphism composition;
- associative scan equivalence at operator level;
- sparsemax/Haar/Walsh-Rademacher finite representation composition;
- finite DPG actor/critic transport with critic max-bootstrap relation.

A strict Noisy Net dominance theorem over MR15 or OpenES still needs a method-state simulation whose image is preserved by the recurrent transition. The safe conclusion is a structural extension of the theorem surface, not a total ordering of methods.

The recurrent scan is compatible with structured semiseparable reasoning only at the algebraic operator level: a Mobius endomorphism composes associatively, so a balanced scan can reproduce sequential composition. This establishes an associative-scan theorem without claiming a separate matrix-factorization theorem.
