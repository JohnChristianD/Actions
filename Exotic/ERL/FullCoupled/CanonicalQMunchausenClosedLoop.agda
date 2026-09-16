{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalQMunchausenClosedLoop where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _<ᵇ_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

data MunchausenMode : Set where
  standardMunchausenMode : MunchausenMode
  negativeQMunchausenMode : MunchausenMode

record SignedFiniteScale : Set where
  constructor signedFiniteScale
  field scaleNegative magnitude : Int8
open SignedFiniteScale public

standardMunchausenScale8 : SignedFiniteScale
standardMunchausenScale8 = signedFiniteScale zero8 (int8OfNat 16)

negativeQMunchausenScale8 : SignedFiniteScale
negativeQMunchausenScale8 = signedFiniteScale one8 (int8OfNat 16)

negativeQMunchausenScale8-law :
  negativeQMunchausenScale8 ≡ signedFiniteScale one8 (int8OfNat 16)
negativeQMunchausenScale8-law = refl

-- Finite endogenous q-log carrier. This is an exact finite analogue of the
-- q-log policy term used by q-Munchausen, not a claim of real-analytic log equality.
finiteMaxEntQLog8 : Int8 → Int8
finiteMaxEntQLog8 x = int8OfNat (numerator (finiteQLog8 x))

finiteMaxEntQLog8-law : ∀ x →
  finiteMaxEntQLog8 x ≡ int8OfNat (numerator (finiteQLog8 x))
finiteMaxEntQLog8-law x = refl

signedScaleCode : SignedFiniteScale → Int8 → Int8
signedScaleCode (signedFiniteScale sign magnitude) x with toℕ (code sign)
... | zero = int8Mul magnitude x
... | _ = int8OfNat (256 ∸ toℕ (code (int8Mul magnitude x)))

munchausenScale : MunchausenMode → SignedFiniteScale
munchausenScale standardMunchausenMode = standardMunchausenScale8
munchausenScale negativeQMunchausenMode = negativeQMunchausenScale8

munchausenShapedReward : MunchausenMode → Int8 → Int8 → Int8
munchausenShapedReward mode reward logPi =
  int8Add reward (signedScaleCode (munchausenScale mode) (finiteMaxEntQLog8 logPi))

shapedRewardCode : MunchausenMode → Int8 → Int8 → Int8
shapedRewardCode = munchausenShapedReward

standardQMunchausen-is-positive :
  munchausenScale standardMunchausenMode ≡ standardMunchausenScale8
standardQMunchausen-is-positive = refl

negativeQMunchausen-is-sign-flipped :
  munchausenScale negativeQMunchausenMode ≡ negativeQMunchausenScale8
negativeQMunchausen-is-sign-flipped = refl

record ClosedLoopKernel : Set₁ where
  constructor closedLoopKernel
  field
    base : FullLearnerKernel
open ClosedLoopKernel public

policyAction2 : FullLearnerKernel → FullLearnerState → Fin 2
policyAction2 K s with policyChoosesLeft (canonicalPolicy K s)
... | enabled = fromℕ< (m%n<n 0 2)
... | disabled = fromℕ< (m%n<n 1 2)

closedLoopCriticReward : MunchausenMode → FullLearnerState → Int8 → CriticState
closedLoopCriticReward mode s reward =
  let q = critic (watkins s)
      shaped = munchausenShapedReward mode reward (policyLeftWeight (canonicalPolicy learnerKernel s))
  in criticState
    (int8Add (qLeft q) shaped)
    (qRight q)

closedLoopWatkins : MunchausenMode → FullLearnerState → Int8 → WatkinsState
closedLoopWatkins mode s reward =
  watkinsState
    (closedLoopCriticReward mode s reward)
    (shapedRewardCode mode reward (policyLeftWeight (canonicalPolicy learnerKernel s)))
    (trace (watkins s))

closedLoopStepMode : FullLearnerKernel → MunchausenMode → FullLearnerState → Fin 2 → Int8 → FullLearnerState
closedLoopStepMode K mode s action reward =
  fullLearnerState
    (suc (clock s))
    (closedLoopWatkins mode s reward)
    (attention s)
    (gruStep (gru s) (canonicalSignal K s))
    (canonicalOptimizerStep K s)
    (norm s)
    (updateLCBCount (fixedTemperatureSparsemax
      (actionScore (qLeft (critic (watkins s))) (qRight (critic (watkins s))))) (lcbCounts s))
    (canonicalQLogControlStep K s)
    (canonicalQLogStep K s)

closedLoopStepMode-clock : ∀ K mode s action reward →
  clock (closedLoopStepMode K mode s action reward) ≡ suc (clock s)
closedLoopStepMode-clock K mode s action reward = refl

closedLoopMode-separation :
  shapedRewardCode standardMunchausenMode one8 one8 ≢
  shapedRewardCode negativeQMunchausenMode one8 one8
closedLoopMode-separation neq = neq refl

record ActionAdapter (N : Nat) : Set₁ where
  constructor actionAdapter
  field
    lift : Fin 2 → Fin N
    project : Fin N → Fin 2
open ActionAdapter public

binaryIdentityAdapter : ActionAdapter 2
binaryIdentityAdapter = actionAdapter (λ a → a) (λ a → a)

mazeAdapter : ActionAdapter 4
mazeAdapter = actionAdapter
  (λ a with toℕ a
   ... | zero = fromℕ< (m%n<n 0 4)
   ... | _ = fromℕ< (m%n<n 1 4))
  (λ a with toℕ a
   ... | zero = fromℕ< (m%n<n 0 2)
   ... | _ = fromℕ< (m%n<n 1 2))

lbfAdapter : ActionAdapter 6
lbfAdapter = actionAdapter
  (λ a with toℕ a
   ... | zero = fromℕ< (m%n<n 0 6)
   ... | _ = fromℕ< (m%n<n 4 6))
  (λ a with toℕ a
   ... | suc (suc (suc (suc zero))) = fromℕ< (m%n<n 1 2)
   ... | _ = fromℕ< (m%n<n 0 2))

pongAdapter : ActionAdapter 3
pongAdapter = actionAdapter
  (λ a with toℕ a
   ... | zero = fromℕ< (m%n<n 0 3)
   ... | _ = fromℕ< (m%n<n 2 3))
  (λ a with toℕ a
   ... | suc (suc zero) = fromℕ< (m%n<n 1 2)
   ... | _ = fromℕ< (m%n<n 0 2))

discountingAdapter : ActionAdapter 5
discountingAdapter = actionAdapter
  (λ a with toℕ a
   ... | zero = fromℕ< (m%n<n 0 5)
   ... | _ = fromℕ< (m%n<n 4 5))
  (λ a with toℕ a
   ... | suc (suc (suc (suc zero))) = fromℕ< (m%n<n 1 2)
   ... | _ = fromℕ< (m%n<n 0 2))

rockSampleAdapter : ActionAdapter 6
rockSampleAdapter = lbfAdapter

record EpisodeSpec (N : Nat) (S : Set) : Set₁ where
  constructor episodeSpec
  field
    adapter : ActionAdapter N
    initial : S
    horizon : Nat
    reference : Nat
    step : Fin N → S → P.StepResult S
    success : Nat → S → Nat
open EpisodeSpec public

record EpisodeRun (S : Set) : Set where
  constructor episodeRun
  field
    finalState : S
    finalLearner : FullLearnerState
    totalReturn steps : Nat
open EpisodeRun public

runEpisode : ∀ {N S} → EpisodeSpec N S → MunchausenMode → FullLearnerState → EpisodeRun S
runEpisode spec mode learner =
  loop (horizon spec) learner (initial spec) zero zero
  where
    loop : Nat → FullLearnerState → S → Nat → Nat → EpisodeRun S
    loop zero l e total steps = episodeRun e l total steps
    loop (suc n) l e total steps with step spec (lift (adapter spec) (policyAction2 learnerKernel l)) e
    ... | P.stepResult obs e' reward done with done
    ...   | P.yes = episodeRun e' 
        (closedLoopStepMode learnerKernel mode l (project (adapter spec) (lift (adapter spec) (policyAction2 learnerKernel l))) (int8OfNat (toℕ (P.code reward))))
        (total + toℕ (P.code reward)) (suc steps)
    ...   | P.no = loop n
        (closedLoopStepMode learnerKernel mode l (project (adapter spec) (lift (adapter spec) (policyAction2 learnerKernel l))) (int8OfNat (toℕ (P.code reward))))
        e'
        (total + toℕ (P.code reward)) (suc steps)

record EpisodeMetrics (S : Set) : Set where
  constructor episodeMetrics
  field
    return reference regret success steps : Nat
open EpisodeMetrics public

metricsOf : ∀ {N S} → EpisodeSpec N S → MunchausenMode → FullLearnerState → EpisodeMetrics S
metricsOf spec mode learner =
  let r = runEpisode spec mode learner
  in episodeMetrics
    (totalReturn r)
    (reference spec)
    (reference spec ∸ totalReturn r)
    (success spec (totalReturn r) (finalState r))
    (steps r)

cartPoleEpisode : EpisodeSpec 2 P.CartPoleQuantizedState
cartPoleEpisode = episodeSpec
  binaryIdentityAdapter
  (P.cartPoleQuantizedState 1 0 0 0 0)
  16 0
  P.cartPoleQuantizedStep
  (λ total s → 1)

banditBest0Episode : EpisodeSpec 2 P.BernoulliBanditState
banditBest0Episode = episodeSpec
  binaryIdentityAdapter
  (P.bernoulliBanditState 0 0 0 0)
  16 16
  P.bernoulliBanditStep
  (λ total s → 1)

banditBest1Episode : EpisodeSpec 2 P.BernoulliBanditState
banditBest1Episode = episodeSpec
  binaryIdentityAdapter
  (P.bernoulliBanditState 1 0 0 0)
  16 16
  P.bernoulliBanditStep
  (λ total s → 1)

knapsackEpisode : EpisodeSpec 2 P.KnapsackState
knapsackEpisode = episodeSpec
  binaryIdentityAdapter
  (P.knapsackState 0 8 0)
  8 16
  (λ a s with toℕ a
   ... | zero = P.knapsackStep P.chooseItem0 s
   ... | _ = P.knapsackStep P.chooseItem1 s)
  (λ total s with P.natEq (P.value s) 16
   ... | P.yes = 1
   ... | P.no = 0)

mazeEpisode : EpisodeSpec 4 P.MazeState
mazeEpisode = episodeSpec
  mazeAdapter
  (P.mazeState 0 0 4 4 0)
  16 1
  P.mazeStep
  (λ total s with P.natEq (P.row s) (P.goalRow s)
   ... | P.yes with P.natEq (P.col s) (P.goalCol s)
   ...   | P.yes = 1
   ...   | P.no = 0
   ... | P.no = 0)

metaMazeEpisode : EpisodeSpec 4 P.MetaMazeState
metaMazeEpisode = episodeSpec
  mazeAdapter
  (P.metaMazeState 0 0 4 4 0)
  16 10
  P.metaMazeStep
  (λ total s with P.natEq (P.row s) (P.goalRow s)
   ... | P.yes with P.natEq (P.col s) (P.goalCol s)
   ...   | P.yes = 1
   ...   | P.no = 0
   ... | P.no = 0)

fourRoomsEpisode : EpisodeSpec 4 P.MazeState
fourRoomsEpisode = episodeSpec
  mazeAdapter
  (P.mazeState 4 1 8 9 0)
  16 1
  P.fourRoomsStep
  (λ total s with P.natEq (P.row s) (P.goalRow s)
   ... | P.yes with P.natEq (P.col s) (P.goalCol s)
   ...   | P.yes = 1
   ...   | P.no = 0
   ... | P.no = 0)

levelBasedForagingEpisode : EpisodeSpec 6 P.LBFState
levelBasedForagingEpisode = episodeSpec
  lbfAdapter
  (P.lbfState 0 0 1 1 0 1 1 0)
  8 1
  P.lbfStep
  (λ total s with P.natEq (P.foodLevel s) 0
   ... | P.yes = 1
   ... | P.no = 0)

pongEpisode : EpisodeSpec 3 P.PongState
pongEpisode = episodeSpec
  pongAdapter
  (P.pongState 0 0 0 0 1 1 0)
  8 8
  P.pongStep
  (λ total s → 1)

memoryChainEpisode : EpisodeSpec 2 P.MemoryChainState
memoryChainEpisode = episodeSpec
  binaryIdentityAdapter
  (P.memoryChainState 1 1 0)
  6 0
  P.memoryChainStep
  (λ total s → 0)

discountingChainEpisode : EpisodeSpec 5 P.DiscountingChainState
discountingChainEpisode = episodeSpec
  discountingAdapter
  (P.discountingChainState 3 0)
  6 5
  P.discountingChainStep
  (λ total s → 1)

rockSampleEpisode : EpisodeSpec 6 P.RockSampleState
rockSampleEpisode = episodeSpec
  rockSampleAdapter
  (P.rockSampleState 3 0 1 0)
  8 1
  P.rockSampleStep
  (λ total s with P.natEq (P.rockGood s) 0
   ... | P.yes = 1
   ... | P.no = 0)

standardBanditBest0 : EpisodeMetrics P.BernoulliBanditState
standardBanditBest0 = metricsOf banditBest0Episode standardMunchausenMode

negativeBanditBest0 : EpisodeMetrics P.BernoulliBanditState
negativeBanditBest0 = metricsOf banditBest0Episode negativeQMunchausenMode

standardCartPole : EpisodeMetrics P.CartPoleQuantizedState
standardCartPole = metricsOf cartPoleEpisode standardMunchausenMode

negativeCartPole : EpisodeMetrics P.CartPoleQuantizedState
negativeCartPole = metricsOf cartPoleEpisode negativeQMunchausenMode

standardMaze : EpisodeMetrics P.MazeState
standardMaze = metricsOf mazeEpisode standardMunchausenMode

negativeMaze : EpisodeMetrics P.MazeState
negativeMaze = metricsOf mazeEpisode negativeQMunchausenMode

standardMetaMaze : EpisodeMetrics P.MetaMazeState
standardMetaMaze = metricsOf metaMazeEpisode standardMunchausenMode

negativeMetaMaze : EpisodeMetrics P.MetaMazeState
negativeMetaMaze = metricsOf metaMazeEpisode negativeQMunchausenMode

standardFourRooms : EpisodeMetrics P.MazeState
standardFourRooms = metricsOf fourRoomsEpisode standardMunchausenMode

negativeFourRooms : EpisodeMetrics P.MazeState
negativeFourRooms = metricsOf fourRoomsEpisode negativeQMunchausenMode

standardKnapsack : EpisodeMetrics P.KnapsackState
standardKnapsack = metricsOf knapsackEpisode standardMunchausenMode

negativeKnapsack : EpisodeMetrics P.KnapsackState
negativeKnapsack = metricsOf knapsackEpisode negativeQMunchausenMode

standardLevelBasedForaging : EpisodeMetrics P.LBFState
standardLevelBasedForaging = metricsOf levelBasedForagingEpisode standardMunchausenMode

negativeLevelBasedForaging : EpisodeMetrics P.LBFState
negativeLevelBasedForaging = metricsOf levelBasedForagingEpisode negativeQMunchausenMode

standardPong : EpisodeMetrics P.PongState
standardPong = metricsOf pongEpisode standardMunchausenMode

negativePong : EpisodeMetrics P.PongState
negativePong = metricsOf pongEpisode negativeQMunchausenMode

standardMemoryChain : EpisodeMetrics P.MemoryChainState
standardMemoryChain = metricsOf memoryChainEpisode standardMunchausenMode

negativeMemoryChain : EpisodeMetrics P.MemoryChainState
negativeMemoryChain = metricsOf memoryChainEpisode negativeQMunchausenMode

standardDiscountingChain : EpisodeMetrics P.DiscountingChainState
standardDiscountingChain = metricsOf discountingChainEpisode standardMunchausenMode

negativeDiscountingChain : EpisodeMetrics P.DiscountingChainState
negativeDiscountingChain = metricsOf discountingChainEpisode negativeQMunchausenMode

standardRockSample : EpisodeMetrics P.RockSampleState
standardRockSample = metricsOf rockSampleEpisode standardMunchausenMode

negativeRockSample : EpisodeMetrics P.RockSampleState
negativeRockSample = metricsOf rockSampleEpisode negativeQMunchausenMode
