# Agda -> MAlonzo -> Mirth -> Liquid Haskell boundary

Agda is the authoritative dependent proof checker. MAlonzo generates the Haskell backend from the current Agda monoliths, and GHC is invoked during the pipeline so the generated backend is actually compiled.

Mirth then generates the Liquid Haskell target from those current MAlonzo outputs. The generated target imports the exact MAlonzo modules for the current build; it is not a checked-in hand-written bridge.

Liquid Haskell runs against that generated target with Z3. This is a freshness and backend-integration gate: it proves that the current generated target can be consumed by Liquid Haskell. It does not claim that Liquid Haskell has independently reconstructed every Agda theorem or erased dependent proof.

The CI manifest records:

Agda source -> MAlonzo generated Haskell -> Mirth-generated Liquid target -> LiquidHaskell/Z3.

The old SimpleHaskell bridge files were deleted because their refinement contracts were static and could drift away from the Agda source. A future theorem-spec extractor could add genuine generated refinement predicates; until then, the pipeline deliberately makes no stronger semantic claim.
