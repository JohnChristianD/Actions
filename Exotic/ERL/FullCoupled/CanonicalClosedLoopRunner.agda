{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalClosedLoopRunner where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_∸_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalQMunchausenClosedLoop
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

data RewardMode : Set where
  noMunchausenMode : RewardMode
  standardMode : RewardMode
  negativeMode : RewardMode

modeScale : RewardMode → SignedFiniteScale
modeScale noMunchausenMode = signedFiniteScale zero8 zero8
modeScale standardMode = standardMunchausenScale8
modeScale negativeMode = negativeQMunchausenScale8

shapeReward : RewardMode → FullLearnerKernel → FullLearnerState → Int8 → Int8
shapeReward noMunchausenMode K s reward = reward
shapeReward mode K s reward = int8Add reward (signedScaleCode (modeScale mode)
  (finiteMaxEntQLog8 (policyLeftWeight (canonicalPolicy K s))))

shapeReward-noop : ∀ K s reward → shapeReward noMunchausenMode K s reward ≡ reward
shapeReward-noop K s reward = refl

record ActionAdapter (N : Nat) : Set₁ where
  constructor actionAdapter
  field lift project : Fin 2 → Fin N
open ActionAdapter public

binaryAdapter : ActionAdapter 2
binaryAdapter = actionAdapter (λ a → a) (λ a → a)

closedLoopPolicy : FullLearnerKernel → FullLearnerState → Fin 2
closedLoopPolicy K s with policyChoosesLeft (canonicalPolicy K s)
... | enabled = fromℕ< (m%n<n 0 2)
... | disabled = fromℕ< (m%n<n 1 2)

closedLoopCritic : RewardMode → FullLearnerKernel → FullLearnerState → Fin 2 → Int8 → CriticState
closedLoopCritic mode K s a reward with toℕ a
... | zero = criticState (int8Add (qLeft (critic (watkins s))) (shapeReward mode K s reward)) (qRight (critic (watkins s)))
... | _ = criticState (qLeft (critic (watkins s))) (int8Add (qRight (critic (watkins s))) (shapeReward mode K s reward))

faithfulClosedLoopStep : FullLearnerKernel → RewardMode → FullLearnerState → Fin 2 → Int8 → FullLearnerState
faithfulClosedLoopStep K mode s a reward = fullLearnerState
  (suc (clock s))
  (watkinsState (closedLoopCritic mode K s a reward)
    (shapeReward mode K s reward) (trace (watkins s)))
  (attention s)
  (canonicalGRUStep K s)
  (canonicalOptimizerStep K s)
  (norm s)
  (updateLCBCount (canonicalPolicy K s) (lcbCounts s))
  (canonicalQLogControlStep K s)
  (canonicalQLogStep K s)

faithfulClosedLoopStep-clock : ∀ K mode s a reward →
  clock (faithfulClosedLoopStep K mode s a reward) ≡ suc (clock s)
faithfulClosedLoopStep-clock K mode s a reward = refl

record EpisodeSpec (N : Nat) (S : Set) : Set₁ where
  constructor episodeSpec
  field adapter : ActionAdapter N
        initial : S
        horizon reference : Nat
        step : Fin N → S → P.StepResult S
        success : Nat → S → Nat
open EpisodeSpec public

record EpisodeMetrics (S : Set) : Set where
  constructor episodeMetrics
  field return reference regret success steps : Nat
open EpisodeMetrics public

runEpisode : ∀ {N S} → EpisodeSpec N S → RewardMode → FullLearnerState → EpisodeMetrics S
runEpisode spec mode learner = loop (horizon spec) learner (initial spec) zero zero
  where
    loop : Nat → FullLearnerState → S → Nat → Nat → EpisodeMetrics S
    loop zero l e total steps = episodeMetrics total (reference spec) (reference spec ∸ total) (success spec total e) steps
    loop (suc n) l e total steps with step spec (lift (adapter spec) (closedLoopPolicy learnerKernel l)) e
    ... | P.stepResult obs e' reward done with done
    ...   | P.yes = episodeMetrics (total + toℕ (P.code reward)) (reference spec)
          ((reference spec) ∸ (total + toℕ (P.code reward))) (success spec (total + toℕ (P.code reward)) e') (suc steps)
    ...   | P.no = loop n
          (faithfulClosedLoopStep learnerKernel mode l
            (project (adapter spec) (lift (adapter spec) (closedLoopPolicy learnerKernel l)))
            (int8OfNat (toℕ (P.code reward))))
          e' (total + toℕ (P.code reward)) (suc steps)
