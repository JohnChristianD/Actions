{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NormPair where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (Nat)

------------------------------------------------------------------------
-- Finite norm-pair boundary. The pair is data plus the proof that both
-- components refer to the same finite learner state. No continuous-norm
-- claim is smuggled into the Int8 kernel.
------------------------------------------------------------------------

record NormPair : Set where
  constructor normPair
  field
    primalNorm : Nat
    dualNorm : Nat
    witness : primalNorm ≡ dualNorm

open NormPair public

defaultNormPair : NormPair
defaultNormPair = normPair 0 0 refl

preserveNormPair : NormPair → NormPair
preserveNormPair p = p

preserveNormPair-correct :
  ∀ p → preserveNormPair p ≡ p
preserveNormPair-correct p = refl

normPair-reassociation :
  ∀ (p : NormPair) → preserveNormPair (preserveNormPair p) ≡ preserveNormPair p
normPair-reassociation p = refl
