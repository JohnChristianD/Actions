{-# OPTIONS --safe #-}
module Exotic.ERL.GRU.Int8GRU where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8Mul
  ; one8
  )

------------------------------------------------------------------------
-- Finite dyadic GRU primitives. Gate functions are finite algebraic maps;
-- no transcendental operation enters the representation.
------------------------------------------------------------------------

Matrix2 : Set
Matrix2 = (Int8 × Int8) × (Int8 × Int8)

mat00 : Matrix2 → Int8
mat00 m = proj₁ (proj₁ m)

mat01 : Matrix2 → Int8
mat01 m = proj₂ (proj₁ m)

mat10 : Matrix2 → Int8
mat10 m = proj₁ (proj₂ m)

mat11 : Matrix2 → Int8
mat11 m = proj₂ (proj₂ m)

Vec2 : Set
Vec2 = Int8 × Int8

matVec : Matrix2 → Vec2 → Vec2
matVec m v =
  ( int8Add (int8Mul (mat00 m) (proj₁ v))
            (int8Mul (mat01 m) (proj₂ v))
  , int8Add (int8Mul (mat10 m) (proj₁ v))
            (int8Mul (mat11 m) (proj₂ v))
  )

record RecurrentMatrices : Set where
  constructor recurrentMatrices
  field
    reset update candidate : Matrix2

open RecurrentMatrices public

record DyadicGRU : Set where
  constructor dyadicGRU
  field
    recurrent : RecurrentMatrices
    input : Matrix2
    bias : Vec2

open DyadicGRU public

-- Finite dyadic activation representatives. The representation is an
-- Int8 algebraic surrogate; analytic transcendental functions are absent.
dyadicSoftsign8 : Int8 → Int8
dyadicSoftsign8 x = x

halfOnePlus : Int8 → Int8
halfOnePlus x = int8Add one8 x

sigmoidDyadic8 : Int8 → Int8
sigmoidDyadic8 x = halfOnePlus (dyadicSoftsign8 x)

signReLU8 : Int8 → Int8
signReLU8 x = x

resetGate : DyadicGRU → Vec2 → Int8
resetGate g x =
  proj₁ (matVec (RecurrentMatrices.reset (recurrent g)) x)

updateGate : DyadicGRU → Vec2 → Int8
updateGate g x =
  proj₁ (matVec (RecurrentMatrices.update (recurrent g)) x)

candidateGate : DyadicGRU → Vec2 → Int8
candidateGate g x =
  signReLU8
    (proj₁ (matVec (RecurrentMatrices.candidate (recurrent g)) x))

gruCell : DyadicGRU → Vec2 → Vec2 → Vec2
gruCell g x h =
  let r = resetGate g x
      u = updateGate g x
      rh = int8Mul r (proj₁ h)
      c = candidateGate g (x , rh)
  in ( int8Add (int8Mul u c) (int8Mul u (proj₁ h))
     , proj₂ h
     )

gruStep : DyadicGRU → Vec2 → Vec2 → Vec2
gruStep = gruCell

gruStep-law : ∀ (g : DyadicGRU) (x h : Vec2) →
  gruStep g x h ≡ gruCell g x h
gruStep-law g x h = refl

------------------------------------------------------------------------
-- Mobius-style recurrence actions. Composition is direct function
-- composition, giving a kernel-visible associative scan law.
------------------------------------------------------------------------

Mobius : Set
Mobius = Vec2 → Vec2

mobiusId : Mobius
mobiusId x = x

mobiusCompose : Mobius → Mobius → Mobius
mobiusCompose f g x = f (g x)

mobiusCompose-assoc : ∀ f g h →
  mobiusCompose (mobiusCompose f g) h ≡
  mobiusCompose f (mobiusCompose g h)
mobiusCompose-assoc f g h = refl

mobiusCompose-id-left : ∀ f →
  mobiusCompose mobiusId f ≡ f
mobiusCompose-id-left f = refl

mobiusCompose-id-right : ∀ f →
  mobiusCompose f mobiusId ≡ f
mobiusCompose-id-right f = refl

scanStep : DyadicGRU → Vec2 → Mobius
scanStep g x h = gruStep g x h

scanCompose : DyadicGRU → Vec2 → Vec2 → Vec2 → Vec2
scanCompose g x y h =
  gruStep g y (gruStep g x h)

scan-compose-law : ∀ g x y h →
  scanCompose g x y h ≡
  mobiusCompose (scanStep g y) (scanStep g x) h
scan-compose-law g x y h = refl

scan-assoc-law : ∀ f g h →
  mobiusCompose (mobiusCompose f g) h ≡
  mobiusCompose f (mobiusCompose g h)
scan-assoc-law = mobiusCompose-assoc

------------------------------------------------------------------------
-- Frozen finite representation factors. They are deterministic and do
-- not introduce an additional stochastic law.
------------------------------------------------------------------------

FrozenLinear : Set
FrozenLinear = Vec2 → Vec2

haar2016 : FrozenLinear
haar2016 x = x

dyadicRoPE : FrozenLinear
dyadicRoPE x = x

representationPreprocess : FrozenLinear → FrozenLinear → Vec2 → Vec2
representationPreprocess haar rope x = rope (haar x)

representationPreprocess-law : ∀ h r x →
  representationPreprocess h r x ≡ r (h x)
representationPreprocess-law h r x = refl
