{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.FlatDyadic where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl; cong)

flatWeight : Fin 256 → ℕ
flatWeight _ = 1

flatDenominator : ℕ
flatDenominator = 256

sumFin : ∀ {n : ℕ} → (Fin n → ℕ) → ℕ
sumFin {zero} f = 0
sumFin {suc n} f = sumFin (λ i → f (suc i)) + f zero

sumFin-one : ∀ (n : ℕ) → sumFin (λ _ → 1) ≡ n
sumFin-one zero = refl
sumFin-one (suc n) = cong suc (sumFin-one n)

flatWeight-sum : sumFin flatWeight ≡ flatDenominator
flatWeight-sum = sumFin-one 256

flatAny-positive : ∀ (x : Fin 256) → flatWeight x ≡ 1
flatAny-positive x = refl

flatStay-positive : flatWeight zero ≡ 1
flatStay-positive = flatAny-positive zero

flatForward-positive : flatWeight 1 ≡ 1
flatForward-positive = flatAny-positive 1

flatBackward-positive : flatWeight 255 ≡ 1
flatBackward-positive = flatAny-positive 255
