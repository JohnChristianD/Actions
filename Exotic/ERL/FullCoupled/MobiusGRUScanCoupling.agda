{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusGRUScanCoupling where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)
open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

record ScanCell : Set where
  constructor scanCell
  field action : L.MobiusAction
        input : L.Int8
open ScanCell public

applyAction : L.MobiusAction → L.Int8 → L.Int8
applyAction f x = L.run f x

scanOne : ScanCell → L.Int8 → L.Int8
scanOne c x = applyAction (action c) x

scanCompose : L.MobiusAction → L.MobiusAction → L.MobiusAction
scanCompose = L.composeMobius

scanAssoc : ∀ f g h x →
  L.run (scanCompose (scanCompose f g) h) x ≡
  L.run (scanCompose f (scanCompose g h)) x
scanAssoc = L.mobiusAssociative

scanAction : ∀ {n : Nat} → ScanCell → Nat → L.Int8 → L.Int8
scanAction c zero x = x
scanAction c (suc n) x = scanAction c n (scanOne c x)

gruScan : ∀ {n : Nat} → L.GRUState → ScanCell → Nat → L.GRUState

gruScan s c zero = s
gruScan s c (suc n) =
  L.gruStep (gruScan s c n) (scanOne c (L.hiddenState (gruScan s c n)))

persistentScanLaw : ∀ {n : Nat} s c →
  L.gruPersistent (gruScan s c n) ≡ L.gruPersistent s
persistentScanLaw s c zero = refl
persistentScanLaw s c (suc n) =
  trans (L.gruPersistentLaw (gruScan s c n)
    (scanOne c (L.hiddenState (gruScan s c n))))
    (persistentScanLaw s c n)

scanStepCoupling : ∀ {n : Nat} s c →
  L.gruPersistent (gruScan s c n) ≡ L.gruPersistent s
scanStepCoupling = persistentScanLaw

record MobiusGRUAction : Set where
  constructor mobiusGRUAction
  field mobius : L.MobiusAction
        recurrent : L.GRUState → L.Int8 → L.GRUState
open MobiusGRUAction public

liftedStep : MobiusGRUAction → L.GRUState → L.Int8 → L.GRUState
liftedStep a s x = recurrent a s (applyAction (mobius a) x)

liftedPersistentLaw : ∀ a s x →
  L.gruPersistent (liftedStep a s x) ≡ L.gruPersistent s
liftedPersistentLaw a s x =
  L.gruPersistentLaw s (applyAction (mobius a) x)
