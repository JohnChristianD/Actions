{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AdditionalBenchmarkPorts where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n; _%_)

open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

uniformReward : Nat → Nat → Nat → Nat
uniformReward action time arms = (action + time) % arms

record UniformBanditState : Set where
  constructor uniformBanditState
  field arms time bestAction totalReward : Nat
open UniformBanditState public

uniformBanditStep : Fin 2 → UniformBanditState → P.StepResult UniformBanditState
uniformBanditStep a (uniformBanditState arms t best total) =
  let ai = toℕ a
      reward = uniformReward ai t arms
      better = ai
  in P.stepResult
       (P.int8OfNat reward)
       (uniformBanditState arms (suc t) better (total + reward))
       (P.int8OfNat reward)
       P.no

record Game2048State : Set where
  constructor game2048State
  field score maxTile occupied time : Nat
open Game2048State public

-- A deterministic finite projection of the Jumanji Game2048 / Pgx board contract.
-- The projection preserves the four directional actions and monotone score/tile
-- growth while avoiding an embedded board implementation or hidden randomness.
mergeReward : Fin 4 → Game2048State → Nat
mergeReward a s = (toℕ a + occupied  s + maxTile s) % 16

game2048Step : Fin 4 → Game2048State → P.StepResult Game2048State
game2048Step a (game2048State score tile occ t) =
  let r = mergeReward a (game2048State score tile occ t)
      nextTile = tile + (r % 2)
      nextOcc = occ + 1
  in P.stepResult
       (P.int8OfNat nextTile)
       (game2048State (score + r) nextTile nextOcc (suc t))
       (P.int8OfNat r)
       P.no

game2048Initial : Game2048State
game2048Initial = game2048State 0 2 2 0

uniformBanditInitial : UniformBanditState
uniformBanditInitial = uniformBanditState 2 0 0 0

uniformBanditPort : Set
uniformBanditPort = UniformBanditState

game2048Port : Set
game2048Port = Game2048State
