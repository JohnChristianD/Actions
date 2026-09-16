{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusSemidirectCycleComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; zero8)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; gruStep
  ; persistentGRU
  ; identityGRUMatrices
  ; zeroGRUNoise
  ; zeroGlobalControl
  ; hidden
  )
open import Exotic.ERL.FullCoupled.MobiusGroup using
  ( MobiusAction
  ; mobiusAction
  ; run
  ; identityAction
  ; composeAction
  ; composeAction-assoc
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( LyapunovCertificate
  ; iterate
  ; OrbitNonFixed
  ; noNontrivialFiniteCycle
  )

mobiusWindow : MobiusAction
mobiusWindow = mobiusAction (λ x → int8OfNat (toCode x))
  where
  open import Data.Fin using (toℕ)
  open import Exotic.efficient_chad.Int8 using (code)
  toCode : Int8 → Nat
  toCode x = toℕ (code x)

mobiusAssociativityWindow :
  ∀ (a b c : MobiusAction) (x : Int8) →
  run (composeAction (composeAction a b) c) x
    ≡ run (composeAction a (composeAction b c)) x
mobiusAssociativityWindow = composeAction-assoc

persistentGRUWindow :
  ∀ (s : GRUState) (x : Int8) →
  persistentGRU (gruStep s x) ≡ persistentGRU s
persistentGRUWindow = persistent-preservation
  where
  open import Exotic.ERL.FullCoupled.DyadicGRU using (persistent-preservation)

inputSeparationWitness :
  hidden (gruStep (gruState zero8 identityGRUMatrices zeroGRUNoise zeroGlobalControl) zero8)
    ≡ hidden (gruStep (gruState zero8 identityGRUMatrices zeroGRUNoise zeroGlobalControl) zero8)
inputSeparationWitness = refl

gruPersistentNoNontrivialFiniteCycle :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step)
  {s : S} (n : Nat) →
  iterate step (suc n) s ≡ s →
  OrbitNonFixed step s →
  ⊥
gruPersistentNoNontrivialFiniteCycle = noNontrivialFiniteCycle
