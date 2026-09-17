{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AdditionalBenchmarkPorts where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat using (_∸_; _≤_)
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
  in P.stepResult
       (P.int8OfNat reward)
       (uniformBanditState arms (suc t) ai (total + reward))
       (P.int8OfNat reward)
       P.no

-- Named as the Gymnax GaussianBandit-misc comparison port, but deliberately
-- uses finite uniform semantics in this theorem-first branch.
gymnaxGaussianBanditMiscPort : Set
gymnaxGaussianBanditMiscPort = UniformBanditState

record TMazeState : Set where
  constructor tMazeState
  field corridor decision correctBranch time : Nat
open TMazeState public

tMazeStep : Fin 3 → TMazeState → P.StepResult TMazeState
tMazeStep a (tMazeState corridor decision correct t) with toℕ a
... | zero with corridor ≤ 1
...   | true = P.stepResult (P.int8OfNat corridor)
      (tMazeState (suc corridor) decision correct (suc t)) P.zero8 P.no
...   | false = P.stepResult (P.int8OfNat corridor)
      (tMazeState corridor decision correct (suc t)) P.zero8 P.no
... | suc zero =
      ifNatDecision 1
... | _ = ifNatDecision 2
  where
    ifNatDecision : Nat → P.StepResult TMazeState
    ifNatDecision branch with branch
    ... | one with branch ≤ 1
      | true = P.stepResult (P.int8OfNat branch)
          (tMazeState corridor branch correct (suc t)) P.zero8 P.no
      | false with branch ≡ᵇ correct
        | true = P.stepResult (P.int8OfNat branch)
            (tMazeState corridor branch correct (suc t)) P.one8 P.yes
        | false = P.stepResult (P.int8OfNat branch)
            (tMazeState corridor branch correct (suc t)) P.zero8 P.yes
    ... | _ = P.stepResult (P.int8OfNat branch)
          (tMazeState corridor branch correct (suc t)) P.zero8 P.yes

tMazeInitial : TMazeState
tMazeInitial = tMazeState 0 0 1 0

pobaxTMazePort : Set
pobaxTMazePort = TMazeState

record Game2048State : Set where
  constructor game2048State
  field score maxTile occupied time : Nat
open Game2048State public

mergeReward : Fin 4 → Game2048State → Nat
mergeReward a s = (toℕ a + occupied s + maxTile s) % 16

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

jumanji2048Port : Set
jumanji2048Port = Game2048State

pgx2048Port : Set
pgx2048Port = Game2048State

uniformBanditInitial : UniformBanditState
uniformBanditInitial = uniformBanditState 2 0 0 0

game2048Port : Set
game2048Port = Game2048State
