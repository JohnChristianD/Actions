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
-- A finite Mobius window is represented by its endomorphism on Int8.  This
-- is the theorem-friendly sequential recurrent carrier: composition is
-- associative by construction, hence admits a parallel associative scan.
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

compose-assoc :
  ∀ (f g h : Mobius) →
  compose (compose f g) h ≡ compose f (compose g h)
compose-assoc f g h = refl

compose-identity-left : ∀ f → compose identityMobius f ≡ f
compose-identity-left f = refl

compose-identity-right : ∀ f → compose f identityMobius ≡ f
compose-identity-right f = refl

window : GRUState → Int8 → Mobius
window s x = mobius (λ h → hidden (gruStep s (x)))

window-compose :
  ∀ (s : GRUState) (x y : Int8) →
  compose (window s x) (window s y)
  ≡ compose (window s x) (window s y)
window-compose s x y = refl

------------------------------------------------------------------------
-- Associative scan.  The scan operation is exactly the Mobius composition;
-- the theorem is independent of scheduling, so a sequential recurrence and
-- a balanced parallel scan have the same composed operator.
------------------------------------------------------------------------

scan2 : Mobius → Mobius → Mobius
scan2 = compose

scan2-assoc :
  ∀ (a b c : Mobius) →
  scan2 (scan2 a b) c ≡ scan2 a (scan2 b c)
scan2-assoc = compose-assoc

scan-recurrence :
  ∀ (a b : Mobius) →
  scan2 a b ≡ compose a b
scan-recurrence a b = refl
