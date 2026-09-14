{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusGroup where

open import Agda.Builtin.Equality using (_≡_; refl; trans; sym)
open import Exotic.efficient_chad.Int8 using (Int8)

------------------------------------------------------------------------
-- Finite Möbius-action algebra.
--
-- The full endomorphism carrier is a monoid: arbitrary recurrent windows
-- compose associatively, but need not be invertible. The genuine group
-- theorem is therefore stated for the admissible finite bijective subset.
-- This avoids the old defect of calling every Int8 endomorphism a group
-- element without supplying an inverse.
------------------------------------------------------------------------

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
  ∀ (f g h : MobiusAction) (x : Int8) →
  run (composeAction (composeAction f g) h) x
  ≡ run (composeAction f (composeAction g h)) x
composeAction-assoc f g h x = refl

composeAction-left-id :
  ∀ (f : MobiusAction) (x : Int8) →
  run (composeAction identityAction f) x ≡ run f x
composeAction-left-id f x = refl

composeAction-right-id :
  ∀ (f : MobiusAction) (x : Int8) →
  run (composeAction f identityAction) x ≡ run f x
composeAction-right-id f x = refl

record MobiusGroupElement : Set₁ where
  constructor mobiusGroupElement
  field
    action : MobiusAction
    inverseAction : MobiusAction
    leftInverse : ∀ x → run inverseAction (run action x) ≡ x
    rightInverse : ∀ x → run action (run inverseAction x) ≡ x

open MobiusGroupElement public

groupIdentity : MobiusGroupElement
groupIdentity =
  mobiusGroupElement
    identityAction
    identityAction
    (λ x → refl)
    (λ x → refl)

groupCompose : MobiusGroupElement → MobiusGroupElement → MobiusGroupElement
groupCompose f g =
  mobiusGroupElement
    (composeAction (action f) (action g))
    (composeAction (inverseAction g) (inverseAction f))
    leftProof
    rightProof
  where
    leftProof : ∀ x →
      run (composeAction (inverseAction g) (inverseAction f))
        (run (composeAction (action f) (action g)) x) ≡ x
    leftProof x =
      trans
        (composeAction-assoc
          (inverseAction g)
          (inverseAction f)
          (composeAction (action f) (action g)) x)
        (trans
          (leftInverse f (run (action g) x))
          (leftInverse g x))

    rightProof : ∀ x →
      run (composeAction (action f) (action g))
        (run (composeAction (inverseAction g) (inverseAction f)) x) ≡ x
    rightProof x =
      trans
        (composeAction-assoc
          (action f)
          (action g)
          (composeAction (inverseAction g) (inverseAction f)) x)
        (trans
          (rightInverse g (run (inverseAction f) x))
          (rightInverse f x))

groupCompose-assoc :
  ∀ (f g h : MobiusGroupElement) (x : Int8) →
  run (action (groupCompose (groupCompose f g) h)) x
  ≡ run (action (groupCompose f (groupCompose g h))) x
groupCompose-assoc f g h x =
  composeAction-assoc (action f) (action g) (action h) x

group-left-id :
  ∀ (f : MobiusGroupElement) (x : Int8) →
  run (action (groupCompose groupIdentity f)) x ≡ run (action f) x
group-left-id f x = composeAction-left-id (action f) x

group-right-id :
  ∀ (f : MobiusGroupElement) (x : Int8) →
  run (action (groupCompose f groupIdentity)) x ≡ run (action f) x
group-right-id f x = composeAction-right-id (action f) x

inverse-left-law :
  ∀ (f : MobiusGroupElement) (x : Int8) →
  run (inverseAction f) (run (action f) x) ≡ x
inverse-left-law f x = leftInverse f x

inverse-right-law :
  ∀ (f : MobiusGroupElement) (x : Int8) →
  run (action f) (run (inverseAction f) x) ≡ x
inverse-right-law f x = rightInverse f x

------------------------------------------------------------------------
-- Recurrent windows use the monoid carrier unless a concrete inverse proof
-- is supplied. This is the precise closure boundary for GRU composition.
------------------------------------------------------------------------

GRUWindow : Set₁
GRUWindow = MobiusAction

windowProduct : GRUWindow → GRUWindow → GRUWindow
windowProduct = composeAction

windowProduct-assoc :
  ∀ (a b c : GRUWindow) (x : Int8) →
  run (windowProduct (windowProduct a b) c) x
  ≡ run (windowProduct a (windowProduct b c)) x
windowProduct-assoc = composeAction-assoc
