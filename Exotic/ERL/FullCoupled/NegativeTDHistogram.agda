{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NegativeTDHistogram where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; _≟_; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (Nat; zero; suc; _∸_)
open import Exotic.efficient_chad.Int8 using (Int8; code; int8OfNat)
open import Exotic.ERL.FullCoupled.ActualCoupledLearner using (State; start)
open import Exotic.ERL.FullCoupled.CausalReplay using
  ( Transition
  ; reward
  ; phi
  ; nextPhi
  ; zeroTransition
  )
open import Exotic.ERL.Finite.TrueOnlineTD using (tdError)

negate8 : Int8 → Int8
negate8 x = int8OfNat (256 ∸ toℕ (code x))

negativeTD : Transition → State → Int8
negativeTD t s =
  negate8 (tdError (reward t) (nextPhi t) (phi t) (State.critic s))

histogram : List Int8 → Fin 256 → Nat
histogram [] b = zero
histogram (x ∷ xs) b with F._≟_ (code x) b
... | yes _ = suc (histogram xs b)
... | no _ = histogram xs b

fitnessHistogram : List Transition → State → Fin 256 → Nat
fitnessHistogram [] s b = zero
fitnessHistogram (t ∷ ts) s b with F._≟_ (code (negativeTD t s)) b
... | yes _ = suc (fitnessHistogram ts s b)
... | no _ = fitnessHistogram ts s b

zeroNegativeTD : negativeTD zeroTransition start ≡ int8OfNat 0
zeroNegativeTD = refl

-- Fitness is diagnostic only: this module is not imported by the learner transition.
