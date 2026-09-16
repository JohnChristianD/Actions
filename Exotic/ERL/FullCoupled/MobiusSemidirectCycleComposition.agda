{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusSemidirectCycleComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Fin using (toℕ)
open import Exotic.efficient_chad.Int8 using (Int8; code; int8OfNat; zero8)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState; gruStep; persistentGRU; persistent-preservation; hidden )
open import Exotic.ERL.FullCoupled.MobiusGroup using
  ( MobiusAction; run; composeAction; composeAction-assoc )
open import Exotic.ERL.FullCoupled.MobiusRational using (mobiusRatio8)
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( LyapunovCertificate; iterate; OrbitNonFixed; noNontrivialFiniteCycle )

mobiusAssociativityWindow :
  ∀ (a b c : MobiusAction) (x : Int8) →
  run (composeAction (composeAction a b) c) x
    ≡ run (composeAction a (composeAction b c)) x
mobiusAssociativityWindow = composeAction-assoc

persistentGRUWindow :
  ∀ (s : GRUState) (x : Int8) →
  persistentGRU (gruStep s x) ≡ persistentGRU s
persistentGRUWindow = persistent-preservation

inputDrivenZeroLaw :
  ∀ s → hidden (gruStep s zero8) ≡ mobiusRatio8 zero8
inputDrivenZeroLaw s = refl

inputDrivenTwoLaw :
  ∀ s → hidden (gruStep s (int8OfNat 2)) ≡ mobiusRatio8 (int8OfNat 2)
inputDrivenTwoLaw s = refl

gruPersistentNoNontrivialFiniteCycle :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step)
  {s : S} (n : Nat) →
  iterate step (suc n) s ≡ s →
  OrbitNonFixed s →
  ⊥
gruPersistentNoNontrivialFiniteCycle = noNontrivialFiniteCycle
