-- BEGIN MIRTH-SYNC GLOBAL OPTIONS
{-# OPTIONS --lossy-unification --backtracking-instance-search --experimental-lazy-instances --confluence-check --syntactic-equality --polarity --auto-inline --guarded --without-K --exact-split --no-infer-absurd-clauses --level-universe --keep-covering-clauses --no-projection-like --erasure #-}
-- END MIRTH-SYNC GLOBAL OPTIONS


module FullCoupled.Agda2HsSurface where

-- BEGIN MIRTH-SYNC COMMON IMPORTS
-- Mirth-generated contract: this exact block is shared by both monoliths.
open import Prelude
open import Prelude.Nat.Properties using (add-assoc; add-suc-r; ≤-antisym; ≤-trans; n<1+n)
import Prelude.Int.Properties as IntegerProperties
-- END MIRTH-SYNC COMMON IMPORTS


open import Haskell.Prelude

record Counter : Type where
  constructor counter
  field
    totalCount : Nat

stepCounter : Counter -> Counter
stepCounter (counter n) = counter (n + 1)

counterLaw : ∀ c -> totalCount (stepCounter c) ≡ totalCount c + 1
counterLaw (counter n) = refl

{-# COMPILE AGDA2HS Counter #-}
{-# COMPILE AGDA2HS stepCounter #-}
