# Imported Libraries

This page records the direct imports of the principal coupled modules at the documentation baseline.

## `F4HardsignKernel.agda`

`Agda.Builtin.Bool`, `Agda.Builtin.Maybe`, `Agda.Builtin.Nat`, `Data.Fin`, `Data.Fin.Properties`, `Data.Nat`, `Data.Nat.DivMod`, `Relation.Binary.PropositionalEquality`.

## `CanonicalCoupledF4Learner.agda`

`Agda.Builtin.Bool`, `Agda.Builtin.Nat`, `Data.Nat`, `Data.Fin`, `Relation.Binary.PropositionalEquality`, plus `Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith` imported as `L`.

## `CanonicalCoupledCompositionTheorems.agda`

`Relation.Binary.PropositionalEquality`, `Agda.Builtin.Nat`, `Data.Nat`, plus `CanonicalCoupledF4Learner` as `C` and `GeneralFullCoupledLearnerMonolith` as `L`.

## `GeneralFullCoupledLearnerMonolith.agda`

`Agda.Builtin.Nat`, `Level`, `Data.Nat`, `Data.Fin`, `Data.Fin.Properties`, `Data.Nat.DivMod`, `Data.List.Base`, `Data.List.Sort` as `Sort`, `Data.Product`, `Relation.Binary.Bundles`, `Relation.Binary.Construct.On` as `On`, `Relation.Binary.Construct.Flip.EqAndOrd` as `Flip`, and `Data.Product.Relation.Binary.Lex.NonStrict` as `Lex`.

## `GeneralFullCoupledTheoremsMonolith.agda`

`Relation.Binary.PropositionalEquality`, `Agda.Builtin.Nat`, `Agda.Builtin.Int` as `I`, `Data.Nat`, `Data.Nat.Properties`, `Data.Empty`, `Data.Fin`, `Data.Product`, `Data.List.Base`, `Data.List.Sort` as `Sort`, `Data.List.Relation.Unary.Sorted.TotalOrder`, `Data.List.Relation.Binary.Permutation.Propositional`, plus `GeneralFullCoupledLearnerMonolith` as `L`.

## `GeneralReservoirAttractorTheorems.agda`

`Relation.Binary.PropositionalEquality`, `Relation.Nullary`, `Agda.Builtin.Nat`, `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Fin.Properties`, `Data.Product`, plus `GeneralFullCoupledLearnerMonolith` as `L` and `GeneralFullCoupledTheoremsMonolith` as `T`.

## `MonolithCompositeReservoirTheorem.agda`

`Agda.Builtin.Nat`, `Data.Nat`, `Data.Nat.Properties`, `Data.Fin`, `Data.Fin.Properties`, `Data.Product`, `Relation.Binary.PropositionalEquality`, plus `GeneralFullCoupledLearnerMonolith` as `L`.

## CI toolchain

The closure workflow installs Agda 2.8.0 and Agda standard library 2.4, then invokes each target with `agda --safe` under the configured timeout.
