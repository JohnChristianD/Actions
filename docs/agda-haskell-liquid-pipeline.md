# Agda -> MAlonzo -> Liquid Haskell boundary

The pipeline has three distinct proof artifacts.

1. Agda remains the authoritative dependent proof checker.
2. MAlonzo compiles both monoliths to ordinary Haskell-shaped backend code.
3. Liquid Haskell checks a deliberately selected Simple Haskell refinement surface with Z3.

MAlonzo is not a dependent-proof-to-Liquid-Haskell translator. Erased Agda indices/proofs are not reconstructed by Liquid Haskell. The checked bridge therefore names the Agda theorem/semantic surface explicitly and supplies equivalent Haskell refinement contracts for the SMT-decidable fragment.

The generated manifest records:

Agda source -> MAlonzo module -> SimpleHaskell bridge -> LiquidHaskell/Z3.

That manifest is consumed by the Mercury graph and uploaded as CI evidence.

agda2hs is deliberately excluded from this pipeline. Its algebraic benefit is readable Haskell extraction from an older, deliberately restricted Agda/Haskell common subset: algebraic data constructors and erased proof/index arguments map more directly onto idiomatic Haskell. It is not a drop-in replacement for MAlonzo here because current agda2hs targets an older Agda range and does not support the current monolith/stdlib surface.

The missing future step for complete automation is a theorem-spec extractor that converts selected Agda propositions into Liquid Haskell predicates. Until that exists, the bridge is automatic at the orchestration level but not a claim that every MAlonzo definition has been independently reproved by Z3.