{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusGroup where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8)

record MobiusAction : Set₁ where
  constructor mobiusAction
  field
    run : Int8 → Int8
open MobiusAction public

identityAction : MobiusAction
identityAction = mobiusAction (λ x → x)

composeAction : MobiusAction → MobiusAction → MobiusAction
composeAction f g = mobiusAction (λ x → run f (run g x))

composeAction-assoc :
  ∀ f g h x →
  run (composeAction (composeAction f g) h) x
    ≡ run (composeAction f (composeAction g h)) x
composeAction-assoc f g h x = refl
