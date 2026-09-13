{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.F4IntKernel where
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (toℕ)
open import Data.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (_≤?_; yes; no)
open import Exotic.efficient_chad.Int8 using (Int8; code; int8OfNat; int8Add; one8; zero8)
open import Exotic.ERL.Finite.Activation using (softsignQ8)

precisionBits : Nat
precisionBits = 8

mag8 : Int8 → Nat
mag8 x with toℕ (code x) ≤? 127
... | yes _ = toℕ (code x)
... | no _ = 256 ∸ toℕ (code x)

neg8 : Int8 → Int8
neg8 x = int8OfNat (256 ∸ toℕ (code x))

sub8 : Int8 → Int8 → Int8
sub8 x y = int8Add x (neg8 y)

l1Norm6 : Int8 → Int8 → Int8 → Int8 → Int8 → Int8 → Nat
l1Norm6 a b c d e f = mag8 a + mag8 b + mag8 c + mag8 d + mag8 e + mag8 f

pathNorm6 : Int8 → Int8 → Int8 → Int8 → Int8 → Int8 → Nat
pathNorm6 a b c d e f = suc (l1Norm6 a b c d e f)

l2Shrink : Int8 → Int8
l2Shrink x with mag8 x / 8
... | zero = zero8
... | suc n with toℕ (code x) ≤? 127
...   | yes _ = int8OfNat (suc n)
...   | no _ = int8OfNat (256 ∸ suc n)

qSign3 : Int8 → Int8
qSign3 x with mag8 x ≤? 3
... | yes _ = zero8
... | no _ with toℕ (code x) ≤? 127
...   | yes _ = one8
...   | no _ = neg8 one8

record F4State : Set where
  constructor f4
  field theta eFull eQ eResidual lResidual logStep : Int8
open F4State public

zeroF4 : F4State
zeroF4 = f4 zero8 zero8 zero8 zero8 zero8 one8

stepF4 : Int8 → F4State → F4State
stepF4 g s = f4
  (int8Add (theta s) (sub8 (qSign3 (softsignQ8 g)) (l2Shrink (theta s))))
  g
  (softsignQ8 g)
  (sub8 g (softsignQ8 g))
  zero8
  one8

precision-law : precisionBits ≡ 8
precision-law = refl

path-law : pathNorm6 zero8 zero8 zero8 zero8 zero8 zero8 ≡ 1
path-law = refl

l2-law : l2Shrink zero8 ≡ zero8
l2-law = refl

learning-law : theta (stepF4 (int8OfNat 5) zeroF4) ≡ one8
learning-law = refl
