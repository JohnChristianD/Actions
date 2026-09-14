{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DeterministicQSA_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.DeterministicQSA using
  ( HasDecidableEquality
  ; decidableEquality
  ; inj₁
  ; LyapunovCertificate
  ; lyapunovCertificate
  ; UniqueFixedPoint
  ; uniqueFixedPoint
  ; DeterministicQSAStyleCertificate
  ; deterministicQSAStyleCertificate
  ; deterministicQSAStyleConvergence
  ; deterministicQSAStyleNoNontrivialCycle
  ; twoPeriodOne
  ; noTwoStateStrongSupportLyapunov
  ; gruNoNontrivialFiniteCycle
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( Fixed
  ; iterate
  )

data OneState : Set where
  onlyState : OneState

oneStep : OneState → OneState
oneStep onlyState = onlyState

oneDecidable : HasDecidableEquality OneState
oneDecidable = decidableEquality
  (λ onlyState onlyState → inj₁ refl)

oneLyapunov : LyapunovCertificate OneState oneStep
oneLyapunov = lyapunovCertificate
  (λ _ → 0)
  (λ onlyState notFixed → notFixed refl)

oneUnique : UniqueFixedPoint oneStep onlyState
oneUnique = uniqueFixedPoint refl
  (λ { onlyState } fixed → refl)

oneQSA : DeterministicQSAStyleCertificate OneState oneStep
oneQSA = deterministicQSAStyleCertificate
  oneLyapunov
  oneDecidable
  onlyState
  oneUnique

oneConverges = deterministicQSAStyleConvergence oneQSA onlyState

oneNoCycle = deterministicQSAStyleNoNontrivialCycle oneQSA

stochasticPeriodOneCounterexample = twoPeriodOne
stochasticLyapunovDisproof = noTwoStateStrongSupportLyapunov

gruConditionalCycleTheorem = gruNoNontrivialFiniteCycle
