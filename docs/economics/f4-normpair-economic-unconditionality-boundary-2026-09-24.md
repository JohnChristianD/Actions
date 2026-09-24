# F4 / NormPair / economic injectivity boundary

The new theorem record composes three distinct surfaces:

1. Exact F4/NormPair deterministic stability already present on the Agda surface.
2. The NormPair quotient/factor transition theorem, proving policy factorization and transition compatibility.
3. Economic global-square injectivity, derived from the readout-left-inverse law.

F4 coercivity and boundedness are explicit premises here. They are not relabeled consequences of exact F4 step stability. The repository currently uses exact Z-valued arithmetic for the Int8 carrier, and its earlier raw thetaQ boundedness/collision theorem was pruned.

The formal impossibility theorem states that no universal generalized Walrasian equilibrium-existence function can be derived even after adjoining those F4 coercivity/boundedness premises, the NormPair factor-transition certificate, and economic injectivity. The countermodel has singleton carrier spaces, so injectivity and the auxiliary optimization premises can be inhabited while the generalized equilibrium predicate is empty.

Graph route:

F4 coercivity -> F4 boundedness -> F4/NormPair stability -> NormPair factor transition -> GRU-F4 economic injectivity -> convergence/fixed-point/market-clearing bridge -> generalized Walrasian existence.

The edge from economic injectivity directly to existence is explicitly blocked. Thus the missing economic contribution is an existence bridge, not more information-preservation structure.

Compared with standard Arrow-Debreu/McKenzie-style existence, the repository does not claim a new unconditional existence theorem. Standard results typically obtain existence from economic/topological structure such as closed/convex consumption sets, convex and continuous preferences, nonsatiation or related boundary conditions, endowment/interiority conditions, and closed/convex production structure; exact assumptions vary by theorem. The repository's generalized surface intentionally exposes weaker or different preference/production structures and keeps the existence bridge explicit.

The main contribution beyond Agda syntax is the compositional boundary: computational dynamics, optimizer stability, representation injectivity, quotient semantics, economic state transport, market clearing, fixed-point existence, and welfare are kept as separate proof-relevant edges instead of being collapsed into one assertion.
