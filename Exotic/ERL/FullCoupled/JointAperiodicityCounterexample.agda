{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.JointAperiodicityCounterexample where

open import Agda.Builtin.Bool using (Bool; false; true; not)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (¬_)

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

data ExploreStep : Bool → Bool → Set where
  explore : ∀ {x y} → ExploreStep x y

ExplorationIrreducible : Set
ExplorationIrreducible = ∀ x y → ExploreStep x y

explorationIrreducible : ExplorationIrreducible
explorationIrreducible x y = explore

explorationSelfLoop : ∀ x → ExploreStep x x
explorationSelfLoop x = explore

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

jointNoSelf : ∀ {x : Joint} → ¬ JointStep x x
jointNoSelf {false , false} ()
jointNoSelf {false , true} ()
jointNoSelf {true , false} ()
jointNoSelf {true , true} ()

JointSelfLoop : Set
JointSelfLoop = Σ Joint (λ x → JointStep x x)

JointAperiodicity : Set
JointAperiodicity = JointSelfLoop × (∀ x y → Reach JointStep x y)

notJointAperiodic : ¬ JointAperiodicity
notJointAperiodic ((x , p) , r) = jointNoSelf p

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
