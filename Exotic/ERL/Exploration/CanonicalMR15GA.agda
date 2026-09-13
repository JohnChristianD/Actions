{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.CanonicalMR15GA where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; fromℕ<; toℕ)
open import Data.Nat using (ℕ; Nat; zero; suc; _+_; _*_ ; _∸_)
open import Data.Nat.DivMod using (m%n<n; _/_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Exotic.ERL.Exploration.FiniteNoise using
  ( Noise
  ; zero
  ; neg
  ; pos
  )
open import Exotic.ERL.Exploration.DyadicMR15GA using (StepGate; noPerturb; perturb; stepCanonical)

pow2 : ℕ → ℕ
pow2 zero = 1
pow2 (suc n) = pow2 n * 2

Dimension : ℕ
Dimension = 4
PopulationSize : ℕ
PopulationSize = 16

Coordinate : Set
Coordinate = Fin Dimension

Genome : Set
Genome = Fin Dimension → Fin 256

Population : Set
Population = Fin PopulationSize → Genome

Exponent : Set
Exponent = Fin 15

Successes : Set
Successes = Fin 17

mutateTicks : ℕ → Noise → Fin 256 → Fin 256
mutateTicks zero n x = x
mutateTicks (suc k) n x = mutateTicks k n (stepCanonical n x)

mutateGenome : Exponent → Noise → Coordinate → Genome → Genome
mutateGenome e n j g = λ i → mutateCoordinate i where
  mutateCoordinate : Coordinate → Fin 256
  mutateCoordinate i with F._≟_ i j
  ... | yes _ = mutateTicks (pow2 (toℕ e)) n (g i)
  ... | no _ = g i

mutatePopulation : StepGate → Exponent → (Fin PopulationSize → Noise) →
  (Fin PopulationSize → Coordinate) →
  Fin 4 → (Fin 4 → Genome) → Population
mutatePopulation noPerturb e noises coords _ elites =
  λ _ → lookupElite F.zero elites
mutatePopulation perturb e noises coords _ elites =
  λ i →
    let j = coords i
        k = F.fromℕ< (m%n<n (toℕ i) 4)
    in mutateGenome e (noises i) j (lookupElite k elites)

record Vec (A : Set) : ℕ → Set where
  constructor _::_
  field head : A

infixr 5 _∷ᵛ_

data V (A : Set) : ℕ → Set where
  []ᵛ : V A zero
  _∷ᵛ_ : ∀ {n} → A → V A n → V A (suc n)

mapV : ∀ {A B : Set} {n : ℕ} → (A → B) → V A n → V B n
mapV f []ᵛ = []ᵛ
mapV f (x ∷ᵛ xs) = f x ∷ᵛ mapV f xs

allFin : (n : ℕ) → V (Fin n) n
allFin zero = []ᵛ
allFin (suc n) = F.zero ∷ᵛ mapV F.suc (allFin n)

indices16 : V (Fin 16) 16
indices16 = allFin 16

lookupV : ∀ {A : Set} {n : ℕ} → Fin n → V A n → A
lookupV () []ᵛ
lookupV F.zero (x ∷ᵛ xs) = x
lookupV (F.suc i) (x ∷ᵛ xs) = lookupV i xs

insertV : ∀ {n : ℕ} →
  (Fin 16 → Fin 16 → Bool) → Fin 16 →
  V (Fin 16) n → V (Fin 16) (suc n)
insertV cmp x []ᵛ = x ∷ᵛ []ᵛ
insertV cmp x (y ∷ᵛ ys) with cmp x y
... | true = x ∷ᵛ y ∷ᵛ ys
... | false = y ∷ᵛ insertV cmp x ys

sortV : ∀ {n : ℕ} →
  (Fin 16 → Fin 16 → Bool) →
  V (Fin 16) n → V (Fin 16) n
sortV cmp []ᵛ = []ᵛ
sortV cmp (x ∷ᵛ xs) = insertV cmp x (sortV cmp xs)

first4 : ∀ {A : Set} {n : ℕ} →
  V A (suc (suc (suc (suc n)))) → V A 4
first4 (a ∷ᵛ b ∷ᵛ c ∷ᵛ d ∷ᵛ xs) = a ∷ᵛ b ∷ᵛ c ∷ᵛ d ∷ᵛ []ᵛ

natEq : ℕ → ℕ → Bool
natEq zero zero = true
natEq zero (suc n) = false
natEq (suc m) zero = false
natEq (suc m) (suc n) = natEq m n

natLess : ℕ → ℕ → Bool
natLess zero zero = false
natLess zero (suc n) = true
natLess (suc m) zero = false
natLess (suc m) (suc n) = natLess m n

type Fitness : Set
type Fitness = Genome → ℕ

topQuarter : Fitness → Population → V Genome 4
topQuarter fit p =
  mapV
    (λ i → p i)
    (first4 (sortV (better fit p) indices16))
  where
  better : Fitness → Population → Fin 16 → Fin 16 → Bool
  better f q i j =
    let fi = f (q i)
        fj = f (q j)
    in if natLess fj fi
       then true
       else if natEq fi fj
       then natLess (toℕ i) (toℕ j)
       else false

lookupElite : Fin 4 → V Genome 4 → Genome
lookupElite = lookupV

sum4 : (Genome → Coordinate → ℕ) → V Genome 4 → Coordinate → ℕ
sum4 f (a ∷ᵛ b ∷ᵛ c ∷ᵛ d ∷ᵛ []ᵛ) j =
  f a j + f b j + f c j + f d j

meanCoordinate : V Genome 4 → Coordinate → Fin 256
meanCoordinate elite j =
  fromℕ< (m%n<n (sum4 (λ g i → toℕ (g i)) elite j / 4) 256)

meanGenome : V Genome 4 → Genome
meanGenome elite = λ j → meanCoordinate elite j

meanPopulation : Fitness → Population → Genome
meanPopulation fit p = meanGenome (topQuarter fit p)

initialPopulation : Population
initialPopulation _ _ = F.zero

initialMean : Genome
initialMean _ = F.zero

initialExponent : Exponent
initialExponent = F.zero

initialSuccesses : Successes
initialSuccesses = F.zero

record MR15State : Set where
  constructor mr15
  field
    population : Population
    mean : Genome
    exponent : Exponent
    successes : Successes

open MR15State public

initialMR15 : MR15State
initialMR15 = mr15 initialPopulation initialMean initialExponent initialSuccesses

stepTicksZero : mutateTicks 1 pos ≡ stepCanonical pos
stepTicksZero = refl

unitPlusMutation : ∀ (j : Coordinate) (g : Genome) →
  mutateGenome initialExponent pos j g ≡
  λ i → mutate i where
    mutate : Coordinate → Fin 256
    mutate i with F._≟_ i j
    ... | yes _ = fromℕ< (m%n<n (toℕ (g i) + 1) 256)
    ... | no _ = g i
unitPlusMutation j g = refl

unitMinusMutation : ∀ (j : Coordinate) (g : Genome) →
  mutateGenome initialExponent neg j g ≡
  λ i → mutate i where
    mutate : Coordinate → Fin 256
    mutate i with F._≟_ i j
    ... | yes _ = fromℕ< (m%n<n (256 + toℕ (g i) ∸ 1) 256)
    ... | no _ = g i
unitMinusMutation j g = refl

lowerExponent : Exponent → Exponent
lowerExponent e with toℕ e ≤? 0
... | yes _ = e
... | no _ = F.fromℕ< (F.toℕ<n (toℕ e ∸ 1) 15)

raiseExponent : Exponent → Exponent
raiseExponent e with toℕ e ≤? 13
... | yes _ = F.fromℕ< (F.toℕ<n (suc (toℕ e)) 15)
... | no _ = e

oneFifthStepUpdate : Exponent → Successes → Exponent
oneFifthStepUpdate e successes with 5 * toℕ successes ≤? 16
... | yes _ = lowerExponent e
... | no _ = raiseExponent e

oneFifthBelow : ∀ e →
  oneFifthStepUpdate e F.zero ≡ lowerExponent e
oneFifthBelow e = refl

oneFifthAbove : ∀ e →
  oneFifthStepUpdate e (F.suc (F.suc (F.suc (F.suc F.zero)))) ≡
  raiseExponent e
oneFifthAbove e = refl

betterThan : Fitness → Genome → Genome → Bool
betterThan fit a b = natLess (fit b) (fit a)

countSuccessVec : Fitness → Population → Population → V (Fin 16) 16 → ℕ
countSuccessVec fit old new []ᵛ = zero
countSuccessVec fit old new (i ∷ᵛ is) with betterThan fit (new i) (old i)
... | true = suc (countSuccessVec fit old new is)
... | false = countSuccessVec fit old new is

countSuccess : Fitness → Population → Population → Successes
countSuccess fit old new =
  F.fromℕ< (m%n<n (countSuccessVec fit old new indices16) 17)

mutationPopulation : Fitness → StepGate →
  MR15State →
  (Fin 16 → Noise) →
  (Fin 16 → Coordinate) →
  Population
mutationPopulation fit noPerturb state noises coords =
  population state
mutationPopulation fit perturb state noises coords =
  let elite = topQuarter fit (population state)
  in mutatePopulation
       perturb
       (oneFifthStepUpdate (exponent state) (successes state))
       noises
       coords
       F.zero
       elite

generationStep : Fitness → StepGate →
  MR15State →
  (Fin 16 → Noise) →
  (Fin 16 → Coordinate) →
  MR15State
generationStep fit noPerturb state noises coords = state
generationStep fit perturb state noises coords =
  let elite = topQuarter fit (population state)
      e' = oneFifthStepUpdate (exponent state) (successes state)
      p' = mutatePopulation perturb e' noises coords F.zero elite
      m' = meanGenome elite
      s' = countSuccess fit (population state) p'
  in mr15 p' m' e' s'

neutralGeneration : ∀ (fit : Fitness) →
  generationStep fit noPerturb initialMR15
    (λ _ → zero)
    (λ _ → F.zero)
  ≡ initialMR15
neutralGeneration fit = refl

latticeUnitPlus : ∀ (fit : Fitness) (state : MR15State)
  (j : Coordinate) (g : Genome) →
  mutateGenome (exponent state) pos j g ≡
  mutateGenome (exponent state) pos j g
latticeUnitPlus fit state j g = refl

latticeUnitMinus : ∀ (fit : Fitness) (state : MR15State)
  (j : Coordinate) (g : Genome) →
  mutateGenome (exponent state) neg j g ≡
  mutateGenome (exponent state) neg j g
latticeUnitMinus fit state j g = refl
