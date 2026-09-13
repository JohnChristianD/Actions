{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.FiniteNoise where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Nat.DivMod using (m%n<n)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; zero8; one8)

dimension : Nat
dimension = 31

Noise : Set
Noise = Fin dimension

noise : Nat → Noise
noise n = fromℕ< (m%n<n n dimension)

weightNat : Nat → Nat
weightNat 0 = 1
weightNat 1 = 2
weightNat 2 = 3
weightNat 3 = 4
weightNat 4 = 5
weightNat 5 = 6
weightNat 6 = 7
weightNat 7 = 8
weightNat 8 = 9
weightNat 9 = 10
weightNat 10 = 11
weightNat 11 = 12
weightNat 12 = 13
weightNat 13 = 14
weightNat 14 = 15
weightNat 15 = 16
weightNat 16 = 15
weightNat 17 = 14
weightNat 18 = 13
weightNat 19 = 12
weightNat 20 = 11
weightNat 21 = 10
weightNat 22 = 9
weightNat 23 = 8
weightNat 24 = 7
weightNat 25 = 6
weightNat 26 = 5
weightNat 27 = 4
weightNat 28 = 3
weightNat 29 = 2
weightNat 30 = 1
weightNat (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))))))))))))))))) = 0

weight : Noise → Nat
weight n = weightNat (toℕ n)

sumWeights : Nat → Nat
sumWeights zero = zero
sumWeights (suc n) = sumWeights n + weightNat n

totalWeight : sumWeights 31 ≡ 256
totalWeight = refl

noiseCode : Noise → Int8
noiseCode n = int8OfNat (toℕ n + 241)

neg zero pos : Noise
neg = noise 14
zero = noise 15
pos = noise 16

negCode : noiseCode neg ≡ int8OfNat 255
negCode = refl

zeroCode : noiseCode zero ≡ zero8
zeroCode = refl

posCode : noiseCode pos ≡ one8
posCode = refl

zeroHasPositiveMass : weight zero ≡ 16
zeroHasPositiveMass = refl

supportIsInt8 : ∀ n → toℕ n < 31
supportIsInt8 n = toℕ<n n

mirror : Noise → Noise
mirror n = noise (30 ∸ toℕ n)

mirrorInvolution : ∀ n → mirror (mirror n) ≡ n
mirrorInvolution n with toℕ n
... | 0 = refl
... | 1 = refl
... | 2 = refl
... | 3 = refl
... | 4 = refl
... | 5 = refl
... | 6 = refl
... | 7 = refl
... | 8 = refl
... | 9 = refl
... | 10 = refl
... | 11 = refl
... | 12 = refl
... | 13 = refl
... | 14 = refl
... | 15 = refl
... | 16 = refl
... | 17 = refl
... | 18 = refl
... | 19 = refl
... | 20 = refl
... | 21 = refl
... | 22 = refl
... | 23 = refl
... | 24 = refl
... | 25 = refl
... | 26 = refl
... | 27 = refl
... | 28 = refl
... | 29 = refl
... | 30 = refl

weightSymmetric : ∀ n → weight n ≡ weight (mirror n)
weightSymmetric n with toℕ n
... | 0 = refl
... | 1 = refl
... | 2 = refl
... | 3 = refl
... | 4 = refl
... | 5 = refl
... | 6 = refl
... | 7 = refl
... | 8 = refl
... | 9 = refl
... | 10 = refl
... | 11 = refl
... | 12 = refl
... | 13 = refl
... | 14 = refl
... | 15 = refl
... | 16 = refl
... | 17 = refl
... | 18 = refl
... | 19 = refl
... | 20 = refl
... | 21 = refl
... | 22 = refl
... | 23 = refl
... | 24 = refl
... | 25 = refl
... | 26 = refl
... | 27 = refl
... | 28 = refl
... | 29 = refl
... | 30 = refl

unitMinusWitness : noiseCode neg ≡ int8OfNat 255
unitMinusWitness = refl

unitPlusWitness : noiseCode pos ≡ one8
unitPlusWitness = refl
