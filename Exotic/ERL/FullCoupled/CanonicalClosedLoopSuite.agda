{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalClosedLoopSuite where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)
open import Exotic.ERL.FullCoupled.CanonicalClosedLoopRunner
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

takeMaze : ActionAdapter 4
takeMaze = actionAdapter
  (λ a with toℕ a
   ... | zero = fromℕ< (m%n<n 0 4)
   ... | _ = fromℕ< (m%n<n 1 4))
  (λ a with toℕ a
   ... | zero = fromℕ< (m%n<n 0 2)
   ... | _ = fromℕ< (m%n<n 1 2))

takeLBF : ActionAdapter 6
takeLBF = actionAdapter
  (λ a with toℕ a
   ... | zero = fromℕ< (m%n<n 0 6)
   ... | _ = fromℕ< (m%n<n 4 6))
  (λ a with toℕ a
   ... | suc (suc (suc (suc zero))) = fromℕ< (m%n<n 1 2)
   ... | _ = fromℕ< (m%n<n 0 2))

takePong : ActionAdapter 3
takePong = actionAdapter
  (λ a with toℕ a
   ... | zero = fromℕ< (m%n<n 0 3)
   ... | _ = fromℕ< (m%n<n 2 3))
  (λ a with toℕ a
   ... | suc (suc zero) = fromℕ< (m%n<n 1 2)
   ... | _ = fromℕ< (m%n<n 0 2))

take5 : ActionAdapter 5
take5 = actionAdapter
  (λ a with toℕ a
   ... | zero = fromℕ< (m%n<n 0 5)
   ... | _ = fromℕ< (m%n<n 4 5))
  (λ a with toℕ a
   ... | suc (suc (suc (suc zero))) = fromℕ< (m%n<n 1 2)
   ... | _ = fromℕ< (m%n<n 0 2))

take6 : ActionAdapter 6
take6 = takeLBF

cartPole : EpisodeSpec 2 P.CartPoleQuantizedState
cartPole = episodeSpec binaryAdapter (P.cartPoleQuantizedState 1 0 0 0 0) 16 0 P.cartPoleQuantizedStep (λ total s → 0)

bandit0 : EpisodeSpec 2 P.BernoulliBanditState
bandit0 = episodeSpec binaryAdapter (P.bernoulliBanditState 0 0 0 0) 16 16 P.bernoulliBanditStep (λ total s with P.natEq total 16 ... | P.yes = 1 ... | P.no = 0)

bandit1 : EpisodeSpec 2 P.BernoulliBanditState
bandit1 = episodeSpec binaryAdapter (P.bernoulliBanditState 1 0 0 0) 16 16 P.bernoulliBanditStep (λ total s with P.natEq total 16 ... | P.yes = 1 ... | P.no = 0)

knapsack : EpisodeSpec 2 P.KnapsackState
knapsack = episodeSpec binaryAdapter (P.knapsackState 0 8 0) 8 16
  (λ a s with toℕ a ... | zero = P.knapsackStep P.chooseItem0 s ... | _ = P.knapsackStep P.chooseItem1 s)
  (λ total s with P.natEq (P.value s) 16 ... | P.yes = 1 ... | P.no = 0)

maze : EpisodeSpec 4 P.MazeState
maze = episodeSpec takeMaze (P.mazeState 0 0 4 4 0) 16 1 P.mazeStep (λ total s with P.natEq (P.row s) (P.goalRow s) ... | P.yes with P.natEq (P.col s) (P.goalCol s) ... | P.yes = 1 ... | P.no = 0 ... | P.no = 0)

metaMaze : EpisodeSpec 4 P.MetaMazeState
metaMaze = episodeSpec takeMaze (P.metaMazeState 0 0 4 4 0) 16 10 P.metaMazeStep (λ total s with P.natEq (P.row s) (P.goalRow s) ... | P.yes with P.natEq (P.col s) (P.goalCol s) ... | P.yes = 1 ... | P.no = 0 ... | P.no = 0)

fourRooms : EpisodeSpec 4 P.MazeState
fourRooms = episodeSpec takeMaze (P.mazeState 4 1 8 9 0) 16 1 P.fourRoomsStep (λ total s with P.natEq (P.row s) (P.goalRow s) ... | P.yes with P.natEq (P.col s) (P.goalCol s) ... | P.yes = 1 ... | P.no = 0 ... | P.no = 0)

levelBasedForaging : EpisodeSpec 6 P.LBFState
levelBasedForaging = episodeSpec takeLBF (P.lbfState 0 0 1 1 0 1 1 0) 8 1 P.lbfStep (λ total s with P.natEq (P.foodLevel s) 0 ... | P.yes = 1 ... | P.no = 0)

pong : EpisodeSpec 3 P.PongState
pong = episodeSpec takePong (P.pongState 0 0 0 0 1 1 0) 8 8 P.pongStep (λ total s → 1)

memoryChain : EpisodeSpec 2 P.MemoryChainState
memoryChain = episodeSpec binaryAdapter (P.memoryChainState 1 1 0) 6 0 P.memoryChainStep (λ total s → 0)

discountingChain : EpisodeSpec 5 P.DiscountingChainState
discountingChain = episodeSpec take5 (P.discountingChainState 3 0) 6 5 P.discountingChainStep (λ total s → 1)

rockSample : EpisodeSpec 6 P.RockSampleState
rockSample = episodeSpec take6 (P.rockSampleState 3 0 1 0) 8 1 P.rockSampleStep (λ total s with P.natEq (P.rockGood s) 0 ... | P.yes = 1 ... | P.no = 0)

plainBandit0 = runEpisode bandit0 noMunchausenMode learnerInitial
standardBandit0 = runEpisode bandit0 standardMode learnerInitial
negativeBandit0 = runEpisode bandit0 negativeMode learnerInitial
plainBandit1 = runEpisode bandit1 noMunchausenMode learnerInitial
standardBandit1 = runEpisode bandit1 standardMode learnerInitial
negativeBandit1 = runEpisode bandit1 negativeMode learnerInitial

plainCartPole = runEpisode cartPole noMunchausenMode learnerInitial
standardCartPole = runEpisode cartPole standardMode learnerInitial
negativeCartPole = runEpisode cartPole negativeMode learnerInitial

plainKnapsack = runEpisode knapsack noMunchausenMode learnerInitial
standardKnapsack = runEpisode knapsack standardMode learnerInitial
negativeKnapsack = runEpisode knapsack negativeMode learnerInitial

plainMaze = runEpisode maze noMunchausenMode learnerInitial
standardMaze = runEpisode maze standardMode learnerInitial
negativeMaze = runEpisode maze negativeMode learnerInitial

plainMetaMaze = runEpisode metaMaze noMunchausenMode learnerInitial
standardMetaMaze = runEpisode metaMaze standardMode learnerInitial
negativeMetaMaze = runEpisode metaMaze negativeMode learnerInitial

plainFourRooms = runEpisode fourRooms noMunchausenMode learnerInitial
standardFourRooms = runEpisode fourRooms standardMode learnerInitial
negativeFourRooms = runEpisode fourRooms negativeMode learnerInitial

plainLevelBasedForaging = runEpisode levelBasedForaging noMunchausenMode learnerInitial
standardLevelBasedForaging = runEpisode levelBasedForaging standardMode learnerInitial
negativeLevelBasedForaging = runEpisode levelBasedForaging negativeMode learnerInitial

plainPong = runEpisode pong noMunchausenMode learnerInitial
standardPong = runEpisode pong standardMode learnerInitial
negativePong = runEpisode pong negativeMode learnerInitial

plainMemoryChain = runEpisode memoryChain noMunchausenMode learnerInitial
standardMemoryChain = runEpisode memoryChain standardMode learnerInitial
negativeMemoryChain = runEpisode memoryChain negativeMode learnerInitial

plainDiscountingChain = runEpisode discountingChain noMunchausenMode learnerInitial
standardDiscountingChain = runEpisode discountingChain standardMode learnerInitial
negativeDiscountingChain = runEpisode discountingChain negativeMode learnerInitial

plainRockSample = runEpisode rockSample noMunchausenMode learnerInitial
standardRockSample = runEpisode rockSample standardMode learnerInitial
negativeRockSample = runEpisode rockSample negativeMode learnerInitial

modeSeparation :
  shapeReward standardMode learnerKernel learnerInitial one8 ≢
  shapeReward negativeMode learnerKernel learnerInitial one8
modeSeparation eq = eq refl
