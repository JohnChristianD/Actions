{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CurrentLearnerInvariants2 where
open import Agda.Builtin.Equality using (_≡_; refl; cong; sym; trans)
open import Exotic.efficient_chad.Int8 using (Int8; zero8)
open import Exotic.ERL.Finite.Int8Vector using (Int8Vector4; vec4)
open import Exotic.ERL.FullCoupled.ActualCoupledLearner using (State; start; step; network)

networkPreserved : ∀ (r : Int8) (phi nextPhi : Int8Vector4) (s : State) → network (step r phi nextPhi s) ≡ network s
networkPreserved r phi nextPhi s = refl

data Reach : State → State → Set where
  here : ∀ {s} → Reach s s
  there : ∀ {s t u r phi nextPhi} → step r phi nextPhi s ≡ t → Reach t u → Reach s u

networkReachInvariant : ∀ {s t} → Reach s t → network t ≡ network s
networkReachInvariant here = refl
networkReachInvariant (there h r) = trans (cong network (sym h)) (networkPreserved _ _ _ _ |> r)
  where
  _|>_ : ∀ {A B : Set} → A → (A → B) → B
  x |> f = f x

zeroFeature : Int8Vector4
zeroFeature = vec4 zero8 zero8 zero8 zero8

zeroStepAtStart : step zero8 zeroFeature zeroFeature start ≡ start
zeroStepAtStart = refl
