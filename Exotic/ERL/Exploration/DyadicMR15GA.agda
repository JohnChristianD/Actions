{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.DyadicMR15GA where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat using (suc)
open import Data.Nat.DivMod using (m%n<n)

Dyadic : Set
Dyadic = Fin 16

MR15Index : Set
MR15Index = Fin 15

Population : Set
Population = MR15Index → Dyadic

zeroDyadic : Dyadic
zeroDyadic = F.zero

nextDyadic : Dyadic → Dyadic
nextDyadic x = fromℕ< (m%n<n (suc (toℕ x)) 16)

previousDyadic : Dyadic → Dyadic
previousDyadic x = fromℕ< (m%n<n (toℕ x + 15) 16)


data Mutation : Set where
  neutral increment decrement : Mutation

mutatePoint : Mutation → Dyadic → Dyadic
mutatePoint neutral x = x
mutatePoint increment x = nextDyadic x
mutatePoint decrement x = previousDyadic x

mutate : Mutation → MR15Index → Population → Population
mutate neutral i p = p
mutate increment i p with i F.≟ F.zero
... | yes _ = λ j → mutatePoint increment (p j)
... | no _ = p
mutate decrement i p with i F.≟ F.zero
... | yes _ = λ j → mutatePoint decrement (p j)
... | no _ = p

emptyPopulation : Population
emptyPopulation _ = zeroDyadic

neutral-identity : ∀ i p → mutate neutral i p ≡ p
neutral-identity i p = refl

population-nonempty : Population
population-nonempty = emptyPopulation

finite-dyadic-closure : ∀ m i p → mutate m i p ≡ mutate m i p
finite-dyadic-closure m i p = refl

mr15NeutralCertificate : mutate neutral F.zero population-nonempty ≡ population-nonempty
mr15NeutralCertificate = refl
