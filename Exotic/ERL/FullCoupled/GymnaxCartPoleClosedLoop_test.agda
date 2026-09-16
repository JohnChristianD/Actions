{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GymnaxCartPoleClosedLoop_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalLearnerGameExecution_test

-- Finite deterministic CartPole projection. The four physical coordinates
-- live on the same Int8 lattice as the learner. The transition distinguishes
-- the two actions, integrates velocity into position and angular velocity
-- into angle, returns the standard per-step reward-one signal, and terminates
-- on a finite safety envelope or the 500-step horizon. This is an exact finite
-- projection, not a bit-for-bit float32 equivalence claim for upstream JAX.

record GymnaxCartPoleFiniteState : Set where
  constructor cartPoleFiniteState
  field
    position velocity angle angularVelocity : Int8
    time : Nat
open GymnaxCartPoleFiniteState public

gymnaxCartPoleInitial : GymnaxCartPoleFiniteState
gymnaxCartPoleInitial =
  cartPoleFiniteState zero8 zero8 zero8 zero8 zero

data CartPoleAction : Set where
  pushLeft pushRight : CartPoleAction

actionCode : CartPoleAction → Int8
actionCode pushLeft = int8OfNat 255
actionCode pushRight = one8

cartPoleForce : CartPoleAction → Int8
cartPoleForce pushLeft = int8OfNat 252
cartPoleForce pushRight = int8OfNat 4

finiteAbs : Int8 → Nat
finiteAbs x with signedCode x
... | neg n = n
... | zer = zero
... | pos n = n

cartPoleDone : GymnaxCartPoleFiniteState → BoolLike
cartPoleDone s with finiteAbs (position s) <ᵇ 48
... | false = yes
... | true with finiteAbs (angle s) <ᵇ 13
...   | false = yes
...   | true with time s <ᵇ 500
...     | true = no
...     | false = yes

record CartPoleTransition : Set where
  constructor cartPoleTransition
  field
    stateAfter : GymnaxCartPoleFiniteState
    rewardAfter : Int8
    doneAfter : BoolLike
open CartPoleTransition public

cartPoleFiniteStep : CartPoleAction → GymnaxCartPoleFiniteState → CartPoleTransition
cartPoleFiniteStep a s =
  let f = cartPoleForce a
      nextVelocity = int8Add (velocity s) f
      nextPosition = int8Add (position s) nextVelocity
      nextAngularVelocity = int8Add
        (angularVelocity s)
        (int8Add f (angle s))
      nextAngle = int8Add (angle s) nextAngularVelocity
      nextState = cartPoleFiniteState
        nextPosition nextVelocity nextAngle nextAngularVelocity (suc (time s))
  in cartPoleTransition nextState one8 (cartPoleDone nextState)

cartPoleForce-distinguishes-actions :
  cartPoleForce pushLeft ≡ int8OfNat 252 ×
  cartPoleForce pushRight ≡ int8OfNat 4
cartPoleForce-distinguishes-actions = refl , refl

cartPole-step-reward : ∀ a s → rewardAfter (cartPoleFiniteStep a s) ≡ one8
cartPole-step-reward a s = refl

cartPole-step-time : ∀ a s → time (stateAfter (cartPoleFiniteStep a s)) ≡ suc (time s)
cartPole-step-time a s = refl

record GymnaxCartPoleLoop : Set where
  constructor gymnaxCartPoleLoop
  field
    environment : GymnaxCartPoleFiniteState
    learner : FullLearnerState
    totalReturn steps : Nat
open GymnaxCartPoleLoop public

cartPoleLearnerAction : FullLearnerState → CartPoleAction
cartPoleLearnerAction s with toℕ (canonicalBit learnerKernel s)
... | zero = pushLeft
... | suc _ = pushRight

cartPoleClosedLoopStep : GymnaxCartPoleLoop → GymnaxCartPoleLoop
cartPoleClosedLoopStep loop =
  let a = cartPoleLearnerAction (learner loop)
      transition = cartPoleFiniteStep a (environment loop)
      r = rewardAfter transition
  in gymnaxCartPoleLoop
      (stateAfter transition)
      (closedLoopStep learnerKernel (learner loop)
        (fromℕ< (m%n<n (caseAction a) 2)) r)
      (totalReturn loop + toℕ (code r))
      (suc (steps loop))
  where
    caseAction : CartPoleAction → Nat
    caseAction pushLeft = zero
    caseAction pushRight = suc zero

cartPoleInitialLoop : GymnaxCartPoleLoop
cartPoleInitialLoop =
  gymnaxCartPoleLoop gymnaxCartPoleInitial learnerInitial zero zero

cartPoleClosedLoop-one-step-reward :
  totalReturn (cartPoleClosedLoopStep cartPoleInitialLoop) ≡ 1
cartPoleClosedLoop-one-step-reward = refl

cartPoleClosedLoop-one-step-count :
  steps (cartPoleClosedLoopStep cartPoleInitialLoop) ≡ 1
cartPoleClosedLoop-one-step-count = refl

cartPoleClosedLoop-learner-clock :
  clock (learner (cartPoleClosedLoopStep cartPoleInitialLoop)) ≡ 1
cartPoleClosedLoop-learner-clock = refl

-- The loop is action-conditioned: the policy chooses the action, the chosen
-- action determines the environment force, the environment emits reward, and
-- that reward enters the maintained finite critic/attention/GRU/optimizer
-- closed-loop update.
