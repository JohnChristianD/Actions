{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusGRU where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; gruStep
  ; hidden
  )

------------------------------------------------------------------------
-- A finite recurrent window is represented by an endomorphism on Int8.
-- This is a recurrence-composition carrier, not a claim that every such
-- endomorphism is a coefficient-level Möbius transformation.
------------------------------------------------------------------------

record Mobius : Set₁ where
  constructor mobius
  field
    run : Int8 → Int8

open Mobius public

identityMobius : Mobius
identityMobius = mobius (λ x → x)

compose : Mobius → Mobius → Mobius
compose f g = mobius (λ x → run f (run g x))

run-compose :
  ∀ (f g : Mobius) (x : Int8) →
  run (compose f g) x ≡ run f (run g x)
run-compose f g x = refl

compose-assoc :
  ∀ (f g h : Mobius) →
  compose (compose f g) h ≡ compose f (compose g h)
compose-assoc f g h = refl

compose-identity-left : ∀ f → compose identityMobius f ≡ f
compose-identity-left f = refl

compose-identity-right : ∀ f → compose f identityMobius ≡ f
compose-identity-right f = refl

------------------------------------------------------------------------
-- One GRU state induces one finite recurrent transition operator.
------------------------------------------------------------------------

windowStep : GRUState → Mobius
windowStep s = mobius (λ h → hidden (gruStep s h))

windowStep-run :
  ∀ (s : GRUState) (x : Int8) →
  run (windowStep s) x ≡ hidden (gruStep s x)
windowStep-run s x = refl

window : GRUState → Int8 → Mobius
window s x = windowStep s

window-ignore-input :
  ∀ (s : GRUState) (x : Int8) →
  window s x ≡ windowStep s
window-ignore-input s x = refl

------------------------------------------------------------------------
-- Two-step recurrence.  The composed operator executes the later window
-- after the earlier window without introducing a commutativity premise.
------------------------------------------------------------------------

twoStepWindow : GRUState → GRUState → Mobius
twoStepWindow s₁ s₂ = compose (windowStep s₁) (windowStep s₂)

twoStepWindow-run :
  ∀ (s₁ s₂ : GRUState) (x : Int8) →
  run (twoStepWindow s₁ s₂) x
  ≡ hidden (gruStep s₁ (hidden (gruStep s₂ x)))
twoStepWindow-run s₁ s₂ x = refl

threeStepWindow : GRUState → GRUState → GRUState → Mobius
threeStepWindow s₁ s₂ s₃ =
  compose (windowStep s₁) (compose (windowStep s₂) (windowStep s₃))

threeStepWindow-run :
  ∀ (s₁ s₂ s₃ : GRUState) (x : Int8) →
  run (threeStepWindow s₁ s₂ s₃) x
  ≡ hidden
      (gruStep s₁
        (hidden
          (gruStep s₂
            (hidden (gruStep s₃ x)))))
threeStepWindow-run s₁ s₂ s₃ x = refl

------------------------------------------------------------------------
-- Associative scan.  The scan operation is exactly recurrent composition;
-- sequential and balanced regroupings therefore have the same pointwise
-- result.
------------------------------------------------------------------------

scan2 : Mobius → Mobius → Mobius
scan2 = compose

scan2-assoc :
  ∀ (a b c : Mobius) →
  scan2 (scan2 a b) c ≡ scan2 a (scan2 b c)
scan2-assoc = compose-assoc

scan2-assoc-pointwise :
  ∀ (a b c : Mobius) (x : Int8) →
  run (scan2 (scan2 a b) c) x
  ≡ run (scan2 a (scan2 b c)) x
scan2-assoc-pointwise a b c x = refl

scan-recurrence :
  ∀ (a b : Mobius) →
  scan2 a b ≡ compose a b
scan-recurrence a b = refl
