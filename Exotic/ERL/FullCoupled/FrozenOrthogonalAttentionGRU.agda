{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FrozenOrthogonalAttentionGRU where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int as I
open import Data.Fin using (toℕ)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; code)

------------------------------------------------------------------------
-- Frozen two-coordinate transform sandwich.
-- The matrices are represented over exact integers. No floating-point or
-- normalisation is involved in the theorem surface.
------------------------------------------------------------------------

IntVec2 : Set
IntVec2 = I.Int × I.Int

oneI : I.Int
oneI = I.pos 1

negOneI : I.Int
negOneI = I.negsuc 0

zeroI : I.Int
zeroI = I.pos 0

dot2 : IntVec2 → IntVec2 → I.Int
dot2 (a , b) (c , d) = I._+_ (I._*_ a c) (I._*_ b d)

------------------------------------------------------------------------
-- Unnormalised Haar H = [[1,1],[1,-1]].
-- H H^T = 2 I. Thus the rows are orthogonal but not orthonormal.
------------------------------------------------------------------------

haarRow0 : IntVec2
haarRow0 = oneI , oneI

haarRow1 : IntVec2
haarRow1 = oneI , negOneI

haar00 : dot2 haarRow0 haarRow0 ≡ I.pos 2
haar00 = refl

haar11 : dot2 haarRow1 haarRow1 ≡ I.pos 2
haar11 = refl

haar01 : dot2 haarRow0 haarRow1 ≡ zeroI
haar01 = refl

------------------------------------------------------------------------
-- Dimension-two unnormalised Helmert has the same contrast decomposition,
-- up to row/sign convention. Consequently Haar is the cleaner canonical
-- choice here, but the orthogonality theorem is equally elementary.
------------------------------------------------------------------------

helmertRow0 : IntVec2
helmertRow0 = oneI , oneI

helmertRow1 : IntVec2
helmertRow1 = negOneI , oneI

helmert00 : dot2 helmertRow0 helmertRow0 ≡ I.pos 2
helmert00 = refl

helmert11 : dot2 helmertRow1 helmertRow1 ≡ I.pos 2
helmert11 = refl

helmert01 : dot2 helmertRow0 helmertRow1 ≡ zeroI
helmert01 = refl

------------------------------------------------------------------------
-- Sparsemax attention is lifted from its finite Int8/Q7 representation to
-- exact integer coordinates before the frozen linear map is applied.
------------------------------------------------------------------------

liftInt8 : Int8 → I.Int
liftInt8 x = I.pos (toℕ (code x))

liftAttention : Int8 × Int8 → IntVec2
liftAttention (x , y) = liftInt8 x , liftInt8 y

haarApply : IntVec2 → IntVec2
haarApply (x , y) = I._+_ x y , I._-_ x y

helmertApply : IntVec2 → IntVec2
helmertApply (x , y) = I._+_ x y , I._-_ y x

------------------------------------------------------------------------
-- Explicit sandwich boundary: sparsemax attention -> frozen transform ->
-- recurrent interface. The recurrent stage receives the transformed vector;
-- no transform parameters are learned here.
------------------------------------------------------------------------

record AttentionGRUSandwich : Set₁ where
  constructor attentionGRUSandwich
  field
    attention : Int8 × Int8
    transformed : IntVec2
    recurrentInput : IntVec2 → IntVec2
open AttentionGRUSandwich public

sandwichTransform : Int8 × Int8 → IntVec2
sandwichTransform p = haarApply (liftAttention p)

canonicalSandwich :
  ∀ p → AttentionGRUSandwich
canonicalSandwich p =
  attentionGRUSandwich p (sandwichTransform p) haarApply
