{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.JointAperiodicityCounterexample where

open import Agda.Builtin.Bool using (Bool; false; true; not)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

-- A causal replay witness can exist independently of the joint learner chain.
record Transition : Set where
  constructor transition
  field payload : Bool

online : Bool → Bool → Bool
online t s = t

replayOne : Transition → Bool → Bool
replayOne t s = online (Transition.payload t) s

causalOnlineReplay : ∀ (t : Transition) (s : Bool) →
  replayOne t s ≡ online (Transition.payload t) s
causalOnlineReplay t s = refl

-- Exploration is maximally irreducible here: every exploration state can
-- reach every other state in one step, and every state has a self-loop.
data ExploreStep : Bool → Bool → Set where
  explore : ∀ {x y} → ExploreStep x y

ExplorationIrreducible : Set
ExplorationIrreducible = ∀ x y → ExploreStep x y

explorationIrreducible : ExplorationIrreducible
explorationIrreducible x y = explore

explorationSelfLoop : ∀ x → ExploreStep x x
explorationSelfLoop x = explore

-- Joint state = exploration state × learner state.
-- The learner component deterministically toggles on every update.
-- Exploration itself remains completely irreducible.
Joint : Set
Joint = Bool × Bool

data JointStep : Joint → Joint → Set where
  jstep : ∀ {e e' l} →
    JointStep (e , l) (e' , not l)

data Reach {S : Set} (step : S → S → Set) : S → S → Set where
  here : ∀ {x} → Reach step x x
  there : ∀ {x y z} → step x y → Reach step y z → Reach step x z

oneStep : ∀ {e e' l} → Reach JointStep (e , l) (e' , not l)
oneStep = there jstep here

twoStep : ∀ {e e' l} → Reach JointStep (e , l) (e' , l)
twoStep = there jstep (there jstep here)

jointIrreducible : ∀ x y → Reach JointStep x y
jointIrreducible (e , false) (e' , false) = twoStep
jointIrreducible (e , false) (e' , true) = oneStep
jointIrreducible (e , true) (e' , false) = oneStep
jointIrreducible (e , true) (e' , true) = twoStep

-- There is no joint self-loop: the learner bit always toggles.
jointNoSelf : ∀ {x : Joint} → ¬ JointStep x x
jointNoSelf {false , false} ()
jointNoSelf {false , true} ()
jointNoSelf {true , false} ()
jointNoSelf {true , true} ()

JointAperiodicity : Set
JointAperiodicity =
  (∃ λ x → JointStep x x) × (∀ x y → Reach JointStep x y)
  where
  data _∃_ (A : Set) (P : A → Set) : Set where
    witness : (x : A) → P x → A ∃ P

notJointAperiodic : ¬ JointAperiodicity
notJointAperiodic (pair p r) =
  jointNoSelf (witness-proof p)
  where
  data Witness (A : Set) (P : A → Set) : Set where
    witnessProof : (x : A) → P x → Witness A P

  witness-proof :
    (x : Joint × (JointStep x x)) → JointStep (x .proj₁) (x .proj₁)
  witness-proof p = p .proj₂

-- Constructive counterexample to:
--   causal-online-equivalence + exploration-irreducibility
--   ==> joint aperiodicity.
counterexample :
  (∀ (t : Transition) (s : Bool) →
     replayOne t s ≡ online (Transition.payload t) s)
  × (∀ x y → ExploreStep x y)
  × (∀ x y → Reach JointStep x y)
  × ¬ JointAperiodicity
counterexample =
  causalOnlineReplay
  , explorationIrreducible
  , jointIrreducible
  , notJointAperiodic
