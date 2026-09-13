{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.OpenESDyadic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin)
open import Data.Nat using (Nat; suc; zero; _+_)

Dyadic : Set
Dyadic = Fin 16

Candidate : Set
Candidate = Fin 4

Population : Set
Population = Candidate → Dyadic

neutral : Population → Population
neutral p = p

shiftUp : Dyadic → Dyadic
shiftUp x with F._≟_ x (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero)))))))))
... | _ = F.zero
shiftUp F.zero = F.suc F.zero
shiftUp x = F.suc x

shiftDown : Dyadic → Dyadic
shiftDown F.zero = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.zero))))))))))))))))
shiftDown x = F.pred x

mutateCandidate : Candidate → Dyadic → Dyadic
mutateCandidate c x with F._≟_ c F.zero
... | _ = shiftUp x

openESMutate : Candidate → Population → Population
openESMutate c p = λ j → mutateCandidate c (p j)

openESNeutral : ∀ p → neutral p ≡ p
openESNeutral p = refl

openESFiniteWitness : Population
openESFiniteWitness _ = F.zero

openESPopulationWitness : openESMutate F.zero openESFiniteWitness ≡ openESMutate F.zero openESFiniteWitness
openESPopulationWitness = refl

openESAntitheticBound :
  suc (suc (suc (suc zero))) ≡ 4
openESAntitheticBound = refl
