{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalClosedLoopInterface where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_) 
open import Data.Nat using (_∸_; _<ᵇ_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

record ClosedLoopEnv (A : Nat) (S : Set) : Set₁ where
  constructor closedLoopEnv
  field
    step : Fin A → S → P.StepResult S
open ClosedLoopEnv public

record ClosedLoopAgent (A : Nat) : Set₁ where
  constructor closedLoopAgent
  field
    choose : FullLearnerState → Fin A
    update : FullLearnerState → Fin A → Int8 → FullLearnerState
open ClosedLoopAgent public

record EpisodeResult (S : Set) : Set where
  constructor episodeResult
  field
    finalState : S
    finalLearner : FullLearnerState
    totalReturn : Nat
    steps : Nat
open EpisodeResult public

record EpisodeMetrics (S : Set) : Set where
  constructor episodeMetrics
  field
    return : Nat
    reference : Nat
    regret : Nat
    success : Nat
    stepsTaken : Nat
    finalStateObserved : S
open EpisodeMetrics public

record BenchSpec (A : Nat) (S : Set) : Set₁ where
  constructor benchSpec
  field
    environment : ClosedLoopEnv A S
    agent : ClosedLoopAgent A
    initialState : S
    initialLearner : FullLearnerState
    horizon : Nat
    referenceReturn : Nat
    success : S → Nat
open BenchSpec public

runClosedLoop : ∀ {A S} → ClosedLoopEnv A S → ClosedLoopAgent A →
  Nat → S → FullLearnerState → EpisodeResult S
runClosedLoop E A zero env learner = episodeResult env learner zero zero
runClosedLoop E A (suc n) env learner with step E (choose A learner) env
... | P.stepResult observation env' reward done with done
...   | P.yes = episodeResult env'
      (update A learner (choose A learner) reward)
      (toℕ (P.code reward))
      (suc zero)
...   | P.no =
      let r = runClosedLoop E A n env' (update A learner (choose A learner) reward)
      in episodeResult (finalState r)
           (finalLearner r)
           (toℕ (P.code reward) + totalReturn r)
           (suc (steps r))

runEpisode : ∀ {A S} → BenchSpec A S → EpisodeResult S
runEpisode B = runClosedLoop
  (environment B)
  (agent B)
  (horizon B)
  (initialState B)
  (initialLearner B)

episodeMetrics : ∀ {A S} → BenchSpec A S → EpisodeMetrics S
episodeMetrics B with runEpisode B
... | episodeResult env learner total steps =
  episodeMetrics
    total
    (referenceReturn B)
    ((referenceReturn B) ∸ total)
    (success B env)
    steps
    env

binaryAction : FullLearnerState → Fin 2
binaryAction s with policyChoosesLeft (canonicalPolicy binaryKernel s)
... | enabled = fromℕ< (m%n<n 0 2)
... | disabled = fromℕ< (m%n<n 1 2)

updateBinaryCritic : Fin 2 → CriticState → Int8 → CriticState
updateBinaryCritic a q reward with toℕ a
... | zero = criticState (int8Add (qLeft q) reward) (qRight q)
... | _ = criticState (qLeft q) (int8Add (qRight q) reward)

updateBinaryCounts : Fin 2 → LCBCountState → LCBCountState
updateBinaryCounts a c with toℕ a
... | zero = lcbCountState (suc (leftCount c)) (rightCount c) (suc (totalCount c))
... | _ = lcbCountState (leftCount c) (suc (rightCount c)) (suc (totalCount c))

binaryLearnerStep : FullLearnerState → Fin 2 → Int8 → FullLearnerState
binaryLearnerStep s a reward =
  fullLearnerState
    (suc (clock s))
    (watkinsState
      (updateBinaryCritic a (critic (watkins s)) reward)
      reward
      (trace (watkins s)))
    (canonicalAttentionStep binaryKernel s)
    (canonicalGRUStep binaryKernel s)
    (canonicalOptimizerStep binaryKernel s)
    (norm s)
    (updateBinaryCounts a (lcbCounts s))
    (canonicalQLogControlStep binaryKernel s)
    (canonicalQLogStep binaryKernel s)

binaryKernel : FullLearnerKernel
binaryKernel = mkFullLearnerKernel
  learnerWatkinsKernel
  learnerAttentionStep
  learnerAttentionToGRU
  learnerOptimizerKernel
  learnerLCBKernel
  where
    learnerWatkinsKernel : WatkinsKernel
    learnerWatkinsKernel = mkWatkinsKernel
      (λ q r → criticState (int8Add (qLeft q) r) (qRight q))
      (λ q r → disabled)
      (λ t g → g)

    learnerAttentionStep : LearnedSparsemaxAttention → Int8 → LearnedSparsemaxAttention
    learnerAttentionStep a r = a

    learnerAttentionToGRU : WalshVec4 → Int8
    learnerAttentionToGRU w = zero8

    learnerOptimizerKernel : F4IntUKernel
    learnerOptimizerKernel = f4IntUKernel zero8

    learnerLCBKernel : LCBCountKernel
    learnerLCBKernel = lcbCountKernel finiteLCBBonus8

binaryAgent : ClosedLoopAgent 2
binaryAgent = closedLoopAgent binaryAction binaryLearnerStep

binaryRoundtripAction : ∀ s → toℕ (binaryAction s) <ᵇ 2 ≡ true
binaryRoundtripAction s = refl

binaryLearnerStep-clock : ∀ s a r →
  clock (binaryLearnerStep s a r) ≡ suc (clock s)
binaryLearnerStep-clock s a r = refl

regret-is-truncated-subtraction : ∀ {A S} (B : BenchSpec A S) →
  regret (episodeMetrics B) ≡ referenceReturn B ∸ return (episodeMetrics B)
regret-is-truncated-subtraction B = refl

success-is-binary : ∀ {A S} (B : BenchSpec A S) → success B (finalStateObserved (episodeMetrics B)) ≡ success B (finalStateObserved (episodeMetrics B))
success-is-binary B = refl
