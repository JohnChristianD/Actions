{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalFaithfulFixedGamePorts where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _≤_)
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using ()
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalGamePorts
open import Exotic.ERL.FullCoupled.CanonicalFaithfulGameVariants

record FaithfulMemoryChainState : Set where
  constructor faithfulMemoryChainState
  field context query time : Nat
open FaithfulMemoryChainState public

memoryLength : Nat
memoryLength = 5

faithfulMemoryChainStep : Fin 2 → FaithfulMemoryChainState → StepResult FaithfulMemoryChainState
faithfulMemoryChainStep a s with leBool memoryLength (time s)
... | yes with natEq (toℕ a) (context s)
...   | yes = stepResult (int8OfNat (time s)) s (int8OfNat 1) yes
...   | no = stepResult (int8OfNat (time s)) s (int8OfNat 255) yes
... | no =
      stepResult
        (int8OfNat (time s))
        (faithfulMemoryChainState (context s) (query s) (suc (time s)))
        zero8
        no

record FaithfulDiscountingChainState : Set where
  constructor faithfulDiscountingChainState
  field context time : Nat
open FaithfulDiscountingChainState public

discountingRewardTime : Nat → Nat
discountingRewardTime zero = 1
discountingRewardTime (suc zero) = 3
discountingRewardTime (suc (suc zero)) = 10
discountingRewardTime (suc (suc (suc zero))) = 30
discountingRewardTime _ = 100

faithfulDiscountingChainStep : Fin 5 → FaithfulDiscountingChainState → StepResult FaithfulDiscountingChainState
faithfulDiscountingChainStep a s with natEq (time s) zero
... | yes with natEq (suc zero) (discountingRewardTime (toℕ a))
...   | yes = stepResult
      (int8OfNat (toℕ a))
      (faithfulDiscountingChainState (toℕ a) (suc (time s)))
      (int8OfNat 11)
      no
...   | no = stepResult
      (int8OfNat (toℕ a))
      (faithfulDiscountingChainState (toℕ a) (suc (time s)))
      zero8
      no
... | no with natEq (suc (time s)) (discountingRewardTime (context s))
...   | yes = stepResult
      (int8OfNat (context s))
      (faithfulDiscountingChainState (context s) (suc (time s)))
      (int8OfNat 10)
      no
...   | no = stepResult
      (int8OfNat (context s))
      (faithfulDiscountingChainState (context s) (suc (time s)))
      zero8
      no

record FaithfulKnapsackState : Set where
  constructor faithfulKnapsackState
  field packed0 packed1 : BoolLike
        capacity value time : Nat
open FaithfulKnapsackState public

data FaithfulKnapsackAction : Set where
  item0 item1 : FaithfulKnapsackAction

faithfulKnapsackStep : FaithfulKnapsackAction → FaithfulKnapsackState → StepResult FaithfulKnapsackState
faithfulKnapsackStep item0 (faithfulKnapsackState p0 p1 c v t) with p0
... | yes = stepResult (int8OfNat 0) (faithfulKnapsackState p0 p1 c v (suc t)) zero8 yes
... | no with leBool 1 c
...   | no = stepResult (int8OfNat 0) (faithfulKnapsackState p0 p1 c v (suc t)) zero8 yes
...   | yes = stepResult (int8OfNat 0)
      (faithfulKnapsackState yes p1 (c ∸ 1) (v + 2) (suc t))
      (int8OfNat 2)
      no
faithfulKnapsackStep item1 (faithfulKnapsackState p0 p1 c v t) with p1
... | yes = stepResult (int8OfNat 1) (faithfulKnapsackState p0 p1 c v (suc t)) zero8 yes
... | no with leBool 2 c
...   | no = stepResult (int8OfNat 1) (faithfulKnapsackState p0 p1 c v (suc t)) zero8 yes
...   | yes = stepResult (int8OfNat 1)
      (faithfulKnapsackState p0 yes (c ∸ 2) (v + 4) (suc t))
      (int8OfNat 4)
      no

faithfulToyMazeStep : Fin 4 → MazeState → StepResult MazeState
faithfulToyMazeStep a s with mazeMove a (row s , col s)
... | nr , nc with toyMazeOpenExact nr nc
...   | no = stepResult (int8OfNat (row s + col s))
      (mazeState (row s) (col s) (goalRow s) (goalCol s) (suc (time s))) zero8 no
...   | yes with natEq nr (goalRow s)
...     | yes with natEq nc (goalCol s)
...       | yes = stepResult (int8OfNat (nr + nc))
          (mazeState nr nc (goalRow s) (goalCol s) (suc (time s))) one8 yes
...       | no = stepResult (int8OfNat (nr + nc))
          (mazeState nr nc (goalRow s) (goalCol s) (suc (time s))) zero8 no
...     | no = stepResult (int8OfNat (nr + nc))
        (mazeState nr nc (goalRow s) (goalCol s) (suc (time s))) zero8 no

faithfulFixedKnapsackInitial : FaithfulKnapsackState
faithfulFixedKnapsackInitial = faithfulKnapsackState no no 3 0 0

faithfulFixedMazeInitial : MazeState
faithfulFixedMazeInitial = mazeState 0 0 4 4 0

faithfulFixedMemoryInitial : FaithfulMemoryChainState
faithfulFixedMemoryInitial = faithfulMemoryChainState 1 1 0

faithfulFixedDiscountingInitial : FaithfulDiscountingChainState
faithfulFixedDiscountingInitial = faithfulDiscountingChainState 0 0

faithfulFixedProjection-contract :
  FaithfulMemoryChainState × FaithfulDiscountingChainState × FaithfulKnapsackState
faithfulFixedProjection-contract = faithfulFixedMemoryInitial ,
  (faithfulFixedDiscountingInitial , faithfulFixedKnapsackInitial)