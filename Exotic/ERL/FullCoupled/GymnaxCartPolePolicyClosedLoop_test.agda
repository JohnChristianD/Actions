{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GymnaxCartPolePolicyClosedLoop_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Nat using (_<ᵇ_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)

open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalLearnerGameExecution_test
open import Exotic.ERL.FullCoupled.GymnaxCartPoleClosedLoop_test

policyAction : FullLearnerKernel → FullLearnerState → CartPoleAction
policyAction K s with policyChoosesLeft (canonicalPolicy K s)
... | enabled = pushLeft
... | disabled = pushRight

actionFin : CartPoleAction → Fin 2
actionFin pushLeft = fromℕ< (m%n<n 0 2)
actionFin pushRight = fromℕ< (m%n<n 1 2)

record PolicyCartPoleLoop : Set where
  constructor policyCartPoleLoop
  field
    environment : GymnaxCartPoleFiniteState
    learner : FullLearnerState
    totalReturn : Nat
    steps : Nat
    done : BoolLike
open PolicyCartPoleLoop public

policyCartPoleInitial : PolicyCartPoleLoop
policyCartPoleInitial =
  policyCartPoleLoop gymnaxCartPoleInitial learnerInitial zero zero disabled

policyCartPoleStep : PolicyCartPoleLoop → PolicyCartPoleLoop
policyCartPoleStep loop =
  let a = policyAction learnerKernel (learner loop)
      transition = cartPoleFiniteStep a (environment loop)
      r = rewardAfter transition
      learner' = closedLoopStep learnerKernel (learner loop) (actionFin a) r
  in policyCartPoleLoop
      (stateAfter transition)
      learner'
      (totalReturn loop + toℕ (code r))
      (suc (steps loop))
      (doneAfter transition)

policyCartPoleStep1 : PolicyCartPoleLoop
policyCartPoleStep1 = policyCartPoleStep policyCartPoleInitial

policyCartPoleStep2 : PolicyCartPoleLoop
policyCartPoleStep2 = policyCartPoleStep policyCartPoleStep1

policyCartPole-initial-action : policyAction learnerKernel learnerInitial ≡ pushRight
policyCartPole-initial-action = refl

policyCartPole-return2 : totalReturn policyCartPoleStep2 ≡ 2
policyCartPole-return2 = refl

policyCartPole-steps2 : steps policyCartPoleStep2 ≡ 2
policyCartPole-steps2 = refl

policyCartPole-done2 : done policyCartPoleStep2 ≡ enabled
policyCartPole-done2 = refl

policyCartPole-metrics : BenchMetrics GymnaxCartPoleFiniteState
policyCartPole-metrics =
  benchMetrics
    (totalReturn policyCartPoleStep2)
    500
    (500 ∸ totalReturn policyCartPoleStep2)
    0
    (steps policyCartPoleStep2)

policyCartPole-metrics-exact : policyCartPole-metrics ≡ benchMetrics 2 500 498 0 2
policyCartPole-metrics-exact = refl

-- The action is selected from the maintained canonical sparsemax+LCB policy,
-- then passed through the finite CartPole action map; the reward returns from
-- the environment and enters the action-conditioned Watkins/attention/GRU/F4
-- closed-loop state update.
