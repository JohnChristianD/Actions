{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.MR15OneBit where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; _×_; _,_)

BitState : Set
BitState = Fin 8 → Bool

data OneBitAction : Set where
  hold : OneBitAction
  flip : Fin 8 → OneBitAction

flipAt : Fin 8 → BitState → BitState
flipAt i s j with i Data.Fin.≟ j
... | yes _ with s j
...   | false = true
...   | true = false
... | no _ = s j

oneBitStep : OneBitAction → BitState → BitState
oneBitStep hold s = s
oneBitStep (flip i) s = flipAt i s

oneBitNeutralSelfLoop : ∀ s → oneBitStep hold s ≡ s
oneBitNeutralSelfLoop s = refl

data Reach {S : Set} (step : S → S → Set) : S → S → Set where
  here : ∀ {x} → Reach step x x
  there : ∀ {x y z} → step x y → Reach step y z → Reach step x z

oneBitSupport : BitState → BitState → Set
oneBitSupport s t = Σ OneBitAction (λ a → oneBitStep a s ≡ t)

oneBitSelfLoop : BitState → Σ BitState (λ s → oneBitSupport s s)
oneBitSelfLoop = (λ _ → false) , (hold , refl)

OneBitAperiodicityObligation : Set
OneBitAperiodicityObligation =
  (Σ BitState (λ s → oneBitSupport s s)) ×
  (∀ s t → Reach oneBitSupport s t)

-- The first factor is proved here.  Connectivity is intentionally an
-- independent obligation rather than being inferred from the neutral move.
