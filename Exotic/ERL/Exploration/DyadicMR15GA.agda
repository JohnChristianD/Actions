{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.DyadicMR15GA where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using (_≤?_; yes; no)
open import Data.Product using (_×_)
open import Relation.Nullary using (yes; no)
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; zero; neg; pos)

dimension : Nat
dimension = 4
populationSize : Nat
populationSize = 16
Population : Set
Population = Fin dimension → Fin 256
Exponent : Set
Exponent = Fin 15
Coordinate : Set
Coordinate = Fin dimension

data StepGate : Set where
  noPerturb perturb : StepGate

zeroPopulation : Population
zeroPopulation _ = F.zero

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = pow2 n * 2

stepTicks : Exponent → Nat
stepTicks e = pow2 (toℕ e)

stepCanonical : Noise → Fin 256 → Fin 256
stepCanonical n x = fromℕ< (m%n<n (toℕ x + toℕ n + 241) 256)

mutation : StepGate → Noise → Coordinate → Population → Population
mutation noPerturb n j p = p
mutation perturb n j p = λ i → mutateCoordinate i where
  mutateCoordinate : Fin dimension → Fin 256
  mutateCoordinate i with F._≟_ i j
  ... | yes _ = stepCanonical n (p i)
  ... | no _ = p i

noPerturbation-self-loop : ∀ n j p → mutation noPerturb n j p ≡ p
noPerturbation-self-loop n j p = refl

canonicalZero-self-loop : ∀ j p → mutation perturb zero j p ≡ p
canonicalZero-self-loop j p = refl

plusStep : Coordinate → Population → Population
plusStep j p = λ i → mutate i where
  mutate : Fin dimension → Fin 256
  mutate i with F._≟_ i j
  ... | yes _ = fromℕ< (m%n<n (toℕ (p i) + 1) 256)
  ... | no _ = p i

minusStep : Coordinate → Population → Population
minusStep j p = λ i → mutate i where
  mutate i with F._≟_ i j
  ... | yes _ = fromℕ< (m%n<n (256 + toℕ (p i) ∸ 1) 256)
  ... | no _ = p i

unitPlusMutation : ∀ j p → mutation perturb pos j p ≡ plusStep j p
unitPlusMutation j p = refl

unitMinusMutation : ∀ j p → mutation perturb neg j p ≡ minusStep j p
unitMinusMutation j p = refl

data Reach : Population → Population → Set where
  here : ∀ {p} → Reach p p
  there : ∀ {p q r} → Reach p q → Reach q r → Reach p r

MR15ReachabilityObligation : Set
MR15ReachabilityObligation = ∀ p q → Reach p q

MutationSelfLoop : Set
MutationSelfLoop = ∀ n j p → mutation noPerturb n j p ≡ p

MR15AperiodicityObligation : Set
MR15AperiodicityObligation = MutationSelfLoop × MR15ReachabilityObligation

unitExponent : Exponent
unitExponent = F.zero

raiseExponent : Exponent → Exponent
raiseExponent e with toℕ e ≤? 13
... | yes _ = fromℕ< (toℕ<n (suc (toℕ e)) 15)
... | no _ = e

lowerExponent : Exponent → Exponent
lowerExponent e with toℕ e ≤? 0
... | yes _ = e
... | no _ = fromℕ< (toℕ<n (toℕ e ∸ 1) 15)

neutralNoPerturb : ∀ n j p → mutation noPerturb n j p ≡ p
neutralNoPerturb = noPerturbation-self-loop

neutralZero : ∀ j p → mutation perturb zero j p ≡ p
neutralZero = canonicalZero-self-loop

oneFifthStepUpdate : Exponent → Fin (suc populationSize) → Exponent
oneFifthStepUpdate m successes with 5 * toℕ successes ≤? populationSize
... | yes _ = lowerExponent m
... | no _ = raiseExponent m

oneFifthBelow : ∀ m → oneFifthStepUpdate m F.zero ≡ lowerExponent m
oneFifthBelow m = refl

oneFifthAbove : ∀ m → oneFifthStepUpdate m (F.suc (F.suc (F.suc (F.suc F.zero)))) ≡ raiseExponent m
oneFifthAbove m = refl
