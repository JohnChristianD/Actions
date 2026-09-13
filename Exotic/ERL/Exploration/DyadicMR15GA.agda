{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.DyadicMR15GA where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (yes; no)

dimension : Nat
dimension = 4

Population : Set
Population = Fin dimension → Fin 256

Exponent : Set
Exponent = Fin 15

Coordinate : Set
Coordinate = Fin dimension

data Sign : Set where
  minus plus : Sign

data StepGate : Set where
  noPerturb perturb : StepGate

zeroPopulation : Population
zeroPopulation _ = F.zero

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = pow2 n * 2

-- A common 2^-7 fixed-point grid represents dyadic exponents -7..+7.
exponentIndex : Exponent → Nat
exponentIndex e = toℕ e

stepTicks : Exponent → Nat
stepTicks e = pow2 (exponentIndex e)

stepSigned : Sign → Exponent → Fin 256 → Fin 256
stepSigned minus e x = fromℕ< (m%n<n (256 + toℕ x ∸ stepTicks e) 256)
stepSigned plus e x = fromℕ< (m%n<n (toℕ x + stepTicks e) 256)

mutation : StepGate → Exponent → Coordinate → Sign → Population → Population
mutation noPerturb e j s p = p
mutation perturb e j s p = λ i →
  mutateCoordinate i
  where
  mutateCoordinate : Fin dimension → Fin 256
  mutateCoordinate i with F._≟_ i j
  ... | yes _ = stepSigned s e (p i)
  ... | no _ = p i

noPerturbation-self-loop : ∀ e j s p →
  mutation noPerturb e j s p ≡ p
noPerturbation-self-loop e j s p = refl

mutation-support-self-loop : ∀ e j s p →
  mutation noPerturb e j s p ≡ p
mutation-support-self-loop = noPerturbation-self-loop

data Reach : Population → Population → Set where
  here : ∀ {p} → Reach p p
  there : ∀ {p q r} → Reach p q → Reach q r → Reach p r

MR15AperiodicityObligation : Set
MR15AperiodicityObligation =
  (∀ p → Σ Coordinate (λ j → Σ Exponent (λ e → Σ Sign (λ s →
    mutation noPerturb e j s p ≡ p))))
  × (∀ p q → Reach p q)

unitExponent : Exponent
unitExponent = F.zero

unitPlusWitness : stepSigned plus unitExponent F.zero ≡ F.suc F.zero
unitPlusWitness = refl

unitMinusWitness : stepSigned minus unitExponent (F.suc F.zero) ≡ F.zero
unitMinusWitness = refl
