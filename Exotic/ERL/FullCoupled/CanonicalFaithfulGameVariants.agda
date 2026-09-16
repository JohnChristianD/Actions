{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalFaithfulGameVariants where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using ()
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

open import Exotic.ERL.FullCoupled.CanonicalGamePorts

fourRoomsOpen : Nat → Nat → BoolLike
fourRoomsOpen r c with r
... | zero = no
... | suc zero with c
...   | zero = no
...   | suc zero = yes
...   | suc (suc zero) = yes
...   | suc (suc (suc zero)) = yes
...   | suc (suc (suc (suc zero))) = yes
...   | suc (suc (suc (suc (suc zero)))) = yes
...   | suc (suc (suc (suc (suc (suc zero))))) = no
...   | suc (suc (suc (suc (suc (suc (suc zero)))))) = yes
...   | suc (suc (suc (suc (suc (suc (suc (suc zero))))))) = yes
...   | suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = yes
...   | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = yes
...   | _ = no
... | suc (suc zero) with c ≤ 5
...   | false = no
...   | true with c ≥ 7
...     | false = no
...     | true = yes
... | suc (suc (suc zero)) with c ≤ 11
...   | false = no
...   | true with c ≥ 1
...     | false = no
...     | true = yes
... | suc (suc (suc (suc zero))) = fourRoomsOpen 1 c
... | suc (suc (suc (suc (suc zero)))) = fourRoomsOpen 1 c
... | suc (suc (suc (suc (suc (suc zero))))) =
    ifOpen13 c 2 7 11
... | suc (suc (suc (suc (suc (suc (suc zero)))))) =
    ifOpen13 c 1 5 9 11
... | suc (suc (suc (suc (suc (suc (suc (suc zero))))))) = fourRoomsOpen 1 c
... | suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = fourRoomsOpen 1 c
... | suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = fourRoomsOpen 1 c
  where
    ifOpen13 : Nat → Nat → Nat → Nat → BoolLike
    ifOpen13 x a b c with a ≤ x
    ... | false = no
    ... | true with x ≤ c
    ...   | false = no
    ...   | true = yes
    ifOpen13 x a b c = no

-- The Jumanji ToyGenerator is represented directly by a fixed finite wall predicate.
toyMazeOpenExact : Nat → Nat → BoolLike
toyMazeOpenExact zero zero = yes
toyMazeOpenExact zero (suc zero) = no
toyMazeOpenExact zero (suc (suc n)) = yes
toyMazeOpenExact (suc zero) zero = yes
toyMazeOpenExact (suc zero) (suc zero) = no
toyMazeOpenExact (suc zero) (suc (suc zero)) = yes
toyMazeOpenExact (suc zero) (suc (suc (suc n))) = no
toyMazeOpenExact (suc (suc zero)) zero = yes
toyMazeOpenExact (suc (suc zero)) (suc zero) = no
toyMazeOpenExact (suc (suc zero)) (suc (suc n)) = yes
toyMazeOpenExact (suc (suc (suc zero))) zero = yes
toyMazeOpenExact (suc (suc (suc zero))) (suc zero) = yes
toyMazeOpenExact (suc (suc (suc zero))) (suc (suc zero)) = yes
toyMazeOpenExact (suc (suc (suc zero))) (suc (suc (suc n))) = no
toyMazeOpenExact (suc (suc (suc (suc zero)))) c with c ≤ 4
... | false = no
... | true = yes
toyMazeOpenExact _ _ = no
