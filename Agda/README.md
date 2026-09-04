# v147 Agda safe-kernel closure

This branch defines the CI entry point for the finite algebraic v147 development.

The intended source path is:

`Exotic/ERL/FullCoupled/CompleteSafe_v147.agda`

The current audited source is maintained as the corresponding Library artifact in ChatGPT. The branch workflow deliberately refuses to silently substitute a reduced model: it checks the exact source path and then runs `agda --safe` on that file.

The v147 theorem surface closed in the audited source includes:

- `qRunProjectionNonnegative_v147`
- `qProjectionRetraction_v147`
- `qRunTerminalKKT_v147`
- `qTerminalMultiplierUnique_v147`
- `qTerminalProjectionUnique_v147`
- `localVJPChainAppend_v147`
- `lstmForwardAppend_v147`
- `EfficientCHADLSTMTBPTT_v147`
- `coupledQOneStepInvariant_v147`

No CSV, NumPy, training-return, or empirical-data theorem is used by this closure. The proof layer is finite algebraic recursion and equality/order reasoning only.

The CI toolchain uses Cabal only to obtain the Agda executable; the verification command is the Agda kernel with `--safe`.
