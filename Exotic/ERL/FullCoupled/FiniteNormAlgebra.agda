{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.FiniteNormAlgebra where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using ()
open import Data.Nat.DivMod using ()
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

signedMagnitude : Signed → Nat
signedMagnitude (neg n) = n
signedMagnitude zer = zero
signedMagnitude (pos n) = n

int8Magnitude : Int8 → Nat
int8Magnitude x = signedMagnitude (signedCode x)

record TwoLayerScalarWeights : Set where
  constructor twoLayerScalarWeights
  field
    inputWeight outputWeight : Int8
open TwoLayerScalarWeights public

l1WeightNorm : TwoLayerScalarWeights → Nat
l1WeightNorm w = int8Magnitude (inputWeight w) + int8Magnitude (outputWeight w)

onePathNorm : TwoLayerScalarWeights → Nat
onePathNorm w = int8Magnitude (inputWeight w) * int8Magnitude (outputWeight w)

record FiniteOrderedNormPair : Set where
  constructor finiteOrderedNormPair
  field
    l1Value pathValue : Nat
open FiniteOrderedNormPair public

normAlgebra : TwoLayerScalarWeights → FiniteOrderedNormPair
normAlgebra w = finiteOrderedNormPair (l1WeightNorm w) (onePathNorm w)

l1WeightNorm-nonnegative : ∀ w → zero ≤ l1WeightNorm w
l1WeightNorm-nonnegative w = z≤n

onePathNorm-nonnegative : ∀ w → zero ≤ onePathNorm w
onePathNorm-nonnegative w = z≤n

finiteNormOrder : FiniteOrderedNormPair → FiniteOrderedNormPair → Set
finiteNormOrder a b =
  l1Value a ≤ l1Value b × pathValue a ≤ pathValue b

finiteNormOrder-refl : ∀ a → finiteNormOrder a a
finiteNormOrder-refl a =
  natSelfLe (l1Value a) , natSelfLe (pathValue a)

onePathNorm-zero-left : ∀ w → int8Magnitude (inputWeight w) ≡ zero →
  onePathNorm w ≡ zero
onePathNorm-zero-left w h =
  trans
    (cong (λ n → n * int8Magnitude (outputWeight w)) h)
    refl

onePathNorm-zero-right : ∀ w → int8Magnitude (outputWeight w) ≡ zero →
  onePathNorm w ≡ zero
onePathNorm-zero-right w h =
  trans
    (cong (λ n → int8Magnitude (inputWeight w) * n) h)
    refl

finiteNormAlgebra-is-non-ring : ∀ w →
  finiteNormOrder (normAlgebra w) (normAlgebra w)
finiteNormAlgebra-is-non-ring = finiteNormOrder-refl ∘ normAlgebra
