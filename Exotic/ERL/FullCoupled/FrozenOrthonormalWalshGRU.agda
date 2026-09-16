{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FrozenOrthonormalWalshGRU where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (toℕ)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; code)

record HalfInt : Set where
  constructor halfInt
  field numerator : I.Int
open HalfInt public

IntVec4 : Set
IntVec4 = I.Int × (I.Int × (I.Int × I.Int))

WalshVec4 : Set
WalshVec4 = HalfInt × (HalfInt × (HalfInt × HalfInt))

row0 : IntVec4
row0 = I.pos 1 , (I.pos 1 , (I.pos 1 , I.pos 1))

row1 : IntVec4
row1 = I.pos 1 , (I.negsuc 0 , (I.pos 1 , I.negsuc 0))

row2 : IntVec4
row2 = I.pos 1 , (I.pos 1 , (I.negsuc 0 , I.negsuc 0))

row3 : IntVec4
row3 = I.pos 1 , (I.negsuc 0 , (I.negsuc 0 , I.pos 1))

dot4 : IntVec4 → IntVec4 → I.Int
dot4 (a , (b , (c , d))) (e , (f , (g , h))) =
  I._+_ (I._+_ (I._*_ a e) (I._*_ b f))
    (I._+_ (I._*_ c g) (I._*_ d h))

walsh00 : dot4 row0 row0 ≡ I.pos 4
walsh00 = refl

walsh11 : dot4 row1 row1 ≡ I.pos 4
walsh11 = refl

walsh22 : dot4 row2 row2 ≡ I.pos 4
walsh22 = refl

walsh33 : dot4 row3 row3 ≡ I.pos 4
walsh33 = refl

walsh01 : dot4 row0 row1 ≡ I.pos 0
walsh01 = refl

walsh02 : dot4 row0 row2 ≡ I.pos 0
walsh02 = refl

walsh03 : dot4 row0 row3 ≡ I.pos 0
walsh03 = refl

walsh12 : dot4 row1 row2 ≡ I.pos 0
walsh12 = refl

walsh13 : dot4 row1 row3 ≡ I.pos 0
walsh13 = refl

walsh23 : dot4 row2 row3 ≡ I.pos 0
walsh23 = refl

-- The active normalized basis is H₄ / 2. The raw Gram matrix is 4 I,
-- so the fixed dyadic factor 1/2 gives the exact orthonormal basis.
walshOrthonormal :
  dot4 row0 row0 ≡ I.pos 4 ×
  dot4 row1 row1 ≡ I.pos 4 ×
  dot4 row2 row2 ≡ I.pos 4 ×
  dot4 row3 row3 ≡ I.pos 4 ×
  dot4 row0 row1 ≡ I.pos 0 ×
  dot4 row0 row2 ≡ I.pos 0 ×
  dot4 row0 row3 ≡ I.pos 0 ×
  dot4 row1 row2 ≡ I.pos 0 ×
  dot4 row1 row3 ≡ I.pos 0 ×
  dot4 row2 row3 ≡ I.pos 0
walshOrthonormal = walsh00 , (walsh11 , (walsh22 , (walsh33 ,
  (walsh01 , (walsh02 , (walsh03 , (walsh12 , (walsh13 , walsh23))))))))

liftAttention : Int8 × Int8 → IntVec4
liftAttention (x , y) =
  I.pos (toℕ (code x)) ,
  (I.pos (toℕ (code y)) , (I.pos 0 , I.pos 0))

walshHadamardApply : IntVec4 → WalshVec4
walshHadamardApply (a , (b , (c , d))) =
  halfInt (I._+_ (I._+_ a b) (I._+_ c d)) ,
  (halfInt (I._+_ (I._-_ a b) (I._-_ c d)) ,
    (halfInt (I._+_ (I._-_ a b) (I._-_ c d)) ,
      halfInt (I._+_ (I._-_ a b) (I._-_ c d))))

walshDimension : Nat
walshDimension = 4

walshDimensionPowerOfFour : walshDimension ≡ 4
walshDimensionPowerOfFour = refl
