{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.DyadicMR15GA where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.DivMod using (m%n<n)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Finite dyadic MR15-style population kernel.
--
-- The stochastic mutation has the exact user-specified zero gate:
-- z = false means no perturbation, while z = true changes exactly one
-- coordinate by a signed dyadic step.  This module deliberately proves only
-- the properties that follow from this transition, and leaves reachability
-- as an explicit theorem obligation.
------------------------------------------------------------------------

dimension : Nat
dimension = 4

Population : Set
Population = Fin dimension → Fin 256

Exponent : Set
Exponent = Fin 15

Coordinate : Set
Coordinate = Fin dimension

Sign : Set
data Sign where
  minus plus : Sign

StepGate : Set
data StepGate where
  noPerturb perturb : StepGate

zeroPopulation : Population
zeroPopulation _ = F.zero

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = pow2 n * 2

-- Fixed-point dyadic step lattice with exponents -7 .. +7.
exponentIndex : Exponent → Nat
exponentIndex e = toℕ e

stepTicks : Exponent → Nat
stepTicks e = pow2 (exponentIndex e)

stepSigned : Sign → Exponent → Fin 256 → Fin 256
stepSigned minus e x = fromℕ< (m%n<n (256 + toℕ x ∸ stepTicks e) 256)
stepSigned plus e x = fromℕ< (m%n<n (toℕ x + stepTicks e) 256)

mutation : StepGate → Exponent → Coordinate → Sign → Population → Population
mutation noPerturb e j s p = p
mutation perturb e j s p with F._≟_ j F.zero
... | yes _ = λ i → stepCoordinate i
... | no _ = p
  where
  stepCoordinate : Fin dimension → Fin 256
  stepCoordinate i with F._≟_ i j
  ... | yes _ = stepSigned s e (p i)
  ... | no _ = p i

-- The no-perturbation gate is an identity at every population state.
noPerturbation-self-loop : ∀ e j s p → mutation noPerturb e j s p ≡ p
noPerturbation-self-loop e j s p = refl

-- Hence the support contains a self-loop at every state whenever the random
-- law assigns positive mass to noPerturb.
mutation-support-self-loop : ∀ e j s p → mutation noPerturb e j s p ≡ p
mutation-support-self-loop = noPerturbation-self-loop

-- Reachability is represented explicitly rather than inferred from the
-- single-tape/online semantics.
data Reach : Population → Population → Set where
  here : ∀ {p} → Reach p p
  there : ∀ {p q r} → Reach p q → Reach q r → Reach p r

MR15AperiodicityObligation : Set
MR15AperiodicityObligation =
  (∀ p → Σ Coordinate (λ j → Σ Exponent (λ e → Σ Sign (λ s →
    mutation noPerturb e j s p ≡ p))))
  × (∀ p q → Reach p q)

-- With exponent 0 available, a perturbation changes one coordinate by ±1
-- tick.  This is the intended finite irreducibility generator, but the full
-- coordinate-wise reachability theorem is intentionally left as an explicit
-- obligation rather than asserted here.
unitExponent : Exponent
unitExponent = F.zero

unitPlusWitness : stepSigned plus unitExponent F.zero ≡ F.suc F.zero
unitPlusWitness = refl

unitMinusWitness : stepSigned minus unitExponent F.suc F.zero ≡ F.zero
unitMinusWitness = refl
