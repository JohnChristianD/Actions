{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.FiniteNoise where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using (_≤?_; yes; no)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; zero8; one8)

dimension : Nat
dimension = 31

Noise : Set
Noise = Fin dimension

noise : Nat → Noise
noise n = fromℕ< (m%n<n n dimension)

-- D_tri(k) has weights 16-|k| on the support indexed by k+15.
weightNat : Nat → Nat
weightNat n with n ≤? 15
... | yes _ = suc n
... | no _ with n ≤? 30
... | yes _ = 31 ∸ n
... | no _ = zero

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

symmetricCentrePair : weightNat 14 ≡ weightNat 16
symmetricCentrePair = refl

symmetricUnitPair : weightNat 0 ≡ weightNat 30
symmetricUnitPair = refl

unitMinusWitness : noiseCode neg ≡ int8OfNat 255
unitMinusWitness = refl

unitPlusWitness : noiseCode pos ≡ one8
unitPlusWitness = refl
