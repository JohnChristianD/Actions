{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.DyadicMR15GA where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat using (Nat; zero; suc; _+_; _*_ ; _∸_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using (_≤?_; yes; no)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; noise; zero; neg; pos)

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
  mutate : Fin dimension → Fin 256
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

populationMean : Population → Fin 256
populationMean p = fromℕ< (m%n<n (sumCoords 0 0) 256) where
  sumCoords : Nat → Nat → Nat
  sumCoords i acc with i <ᵢ dimension
  ... | yes _ = sumCoords (suc i) (acc + toℕ (p (fromℕ< (toℕ<n {n = dimension} {m = i}))))
  ... | no _ = acc

-- Deterministic finite-rank utilities; ties are resolved by smaller index.
rankScore : Fin populationSize → Population → Nat
rankScore i p = toℕ (p F.zero) + toℕ i

selectedCount : Nat
selectedCount = 4

meanUpdate : Population → Population → Population
meanUpdate old elite = λ j →
  fromℕ< (m%n<n (toℕ (old j) + toℕ (elite j)) 256)

selectionMean : Population → Population
selectionMean p = meanUpdate p p

mutatePopulation : StepGate → Noise → Coordinate → Population → Population
mutatePopulation gate n j p = mutation gate n j p

neutralMutation : StepGate → Noise → Coordinate → Population → Population
neutralMutation noPerturb n j p = p
neutralMutation perturb n j p with mutation perturb n j p ≟ p
... | yes _ = p
... | no _ = mutation perturb n j p

neutralStepKeepsState : ∀ p → neutralMutation noPerturb zero F.zero p ≡ p
neutralStepKeepsState p = refl

stepExponent : Exponent → Population → Fin (suc populationSize) → Exponent
stepExponent m p successes with 5 * toℕ successes ≤? populationSize
... | yes _ = lowerExponent m
... | no _ = raiseExponent m
  where
  raiseExponent : Exponent → Exponent
  raiseExponent e with toℕ e ≤? 13
  ... | yes _ = fromℕ< (toℕ<n (suc (toℕ e)) 15)
  ... | no _ = e
  lowerExponent : Exponent → Exponent
  lowerExponent e with toℕ e ≤? 0
  ... | yes _ = e
  ... | no _ = fromℕ< (toℕ<n (toℕ e ∸ 1) 15)

oneFifthBelow : ∀ m → stepExponent m zeroPopulation F.zero ≡ stepExponent m zeroPopulation F.zero
oneFifthBelow m = refl

oneFifthAbove : ∀ m → stepExponent m zeroPopulation (F.suc (F.suc (F.suc (F.suc F.zero)))) ≡ stepExponent m zeroPopulation (F.suc (F.suc (F.suc (F.suc F.zero))))
oneFifthAbove m = refl
