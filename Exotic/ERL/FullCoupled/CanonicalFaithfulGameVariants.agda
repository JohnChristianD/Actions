{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalFaithfulGameVariants where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using ()
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalGamePorts

orBool : BoolLike → BoolLike → BoolLike
orBool yes _ = yes
orBool _ yes = yes
orBool _ _ = no

between : Nat → Nat → Nat → BoolLike
between lo hi x with lo ≤ x
... | false = no
... | true with x ≤ hi
...   | false = no
...   | true = yes
...   | false = no

-- Exact connectivity of the 13x13 Gymnax FourRooms map.
fourRoomsOpenExact : Nat → Nat → BoolLike
fourRoomsOpenExact zero c = no
fourRoomsOpenExact (suc zero) c = orBool (between 1 5 c) (between 7 11 c)
fourRoomsOpenExact (suc (suc zero)) c = orBool (between 1 5 c) (between 7 11 c)
fourRoomsOpenExact (suc (suc (suc zero))) c = between 1 11 c
fourRoomsOpenExact (suc (suc (suc (suc zero)))) c = orBool (between 1 5 c) (between 7 11 c)
fourRoomsOpenExact (suc (suc (suc (suc (suc zero))))) c = orBool (between 1 5 c) (between 7 11 c)
fourRoomsOpenExact (suc (suc (suc (suc (suc (suc zero)))))) c = orBool (between 2 2 c) (between 7 11 c)
fourRoomsOpenExact (suc (suc (suc (suc (suc (suc (suc zero))))))) c = orBool (between 1 5 c) (between 9 11 c)
fourRoomsOpenExact (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) c = orBool (between 1 5 c) (between 7 11 c)
fourRoomsOpenExact (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) c = orBool (between 1 5 c) (between 7 11 c)
fourRoomsOpenExact (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) c = between 1 11 c
fourRoomsOpenExact (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) c = orBool (between 1 5 c) (between 7 11 c)
fourRoomsOpenExact _ _ = no

-- Jumanji's hardcoded 5x5 ToyGenerator wall layout.
toyMazeOpenExact : Nat → Nat → BoolLike
toyMazeOpenExact zero c = orBool (between 0 0 c) (between 2 4 c)
toyMazeOpenExact (suc zero) c = orBool (between 0 0 c) (between 2 2 c)
toyMazeOpenExact (suc (suc zero)) c = orBool (between 0 0 c) (between 2 4 c)
toyMazeOpenExact (suc (suc (suc zero))) c = between 0 2 c
toyMazeOpenExact (suc (suc (suc (suc zero)))) c = between 0 4 c
toyMazeOpenExact _ _ = no
