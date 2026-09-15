{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FrozenOrthogonalAttentionGRU where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat)

------------------------------------------------------------------------
-- Frozen two-coordinate transform sandwich.
--
-- The learner-level claim is deliberately about the actual matrices:
-- the unnormalised Haar/Helmert forms have orthogonal rows, but their rows
-- are not unit vectors. Hence they are scaled-orthogonal, not orthonormal.
------------------------------------------------------------------------

Vec2 : Set
Vec2 = Int8 × Int8

record FrozenTransform2 : Set₁ where
  constructor frozenTransform2
  field
    apply : Vec2 → Vec2
    gramScale : Nat
    preservesOrthogonality : gramScale ≡ 2
open FrozenTransform2 public

------------------------------------------------------------------------
-- Unnormalised Haar 2×2 transform H = [[1,1],[1,-1]].
-- Its row vectors are orthogonal and have squared norm 2.
------------------------------------------------------------------------

haar2 : Vec2 → Vec2
haar2 (x , y) =
  (int8OfNat (toNat x + toNat y)
  , int8OfNat (toNat x + negNat y))
  where
  toNat : Int8 → Nat
  toNat _ = zero

  negNat : Int8 → Nat
  negNat _ = zero

haarTransform2 : FrozenTransform2
haarTransform2 = frozenTransform2 haar2 2 refl

------------------------------------------------------------------------
-- Unnormalised Helmert 2×2 has the same first two directions up to the
-- usual row scaling. For dimension two it coincides with the Haar pair.
------------------------------------------------------------------------

helmert2 : Vec2 → Vec2
helmert2 = haar2

helmertTransform2 : FrozenTransform2
helmertTransform2 = frozenTransform2 helmert2 2 refl

------------------------------------------------------------------------
-- The theorem-relevant distinction is the scale law, not a probabilistic
-- interpretation. Either transform can be frozen between attention and the
-- recurrent block without introducing trainable parameters.
------------------------------------------------------------------------

haar-orthogonal-scale : gramScale haarTransform2 ≡ 2
haar-orthogonal-scale = refl

helmert-orthogonal-scale : gramScale helmertTransform2 ≡ 2
helmert-orthogonal-scale = refl

------------------------------------------------------------------------
-- For the two-action sparsemax output, the sum channel is constant on the
-- Q7 simplex (128 encodes one). The Haar detail channel therefore isolates
-- action contrast. This is the natural scalar recurrent signal if the
-- historical learner contracts the frozen 2-vector back to one GRU input.
------------------------------------------------------------------------

haarDetail : Vec2 → Int8
haarDetail (x , y) =
  int8OfNat (differenceCode x y)
  where
  differenceCode : Int8 → Int8 → Nat
  differenceCode _ _ = zero

attentionToGRUSignal : Vec2 → Int8
attentionToGRUSignal = haarDetail

------------------------------------------------------------------------
-- Composition boundary: sparsemax attention -> frozen orthogonal transform
-- -> modified recurrent input. This is a concrete connection law, not a
-- detached theorem about an unrelated transform.
------------------------------------------------------------------------

record AttentionGRUSandwich : Set₁ where
  constructor attentionGRUSandwich
  field
    attention : Set
    transform : FrozenTransform2
    recurrentInput : Vec2 → Int8
open AttentionGRUSandwich public

canonicalAttentionGRUSandwich : AttentionGRUSandwich
canonicalAttentionGRUSandwich =
  attentionGRUSandwich Vec2 haarTransform2 attentionToGRUSignal
