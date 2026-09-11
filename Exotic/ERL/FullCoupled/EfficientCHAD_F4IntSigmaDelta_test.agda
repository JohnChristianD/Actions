{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_F4IntSigmaDelta_test where

open import Agda.Builtin.Equality using (_≡_)
open import Exotic.ERL.FullCoupled.EfficientCHAD_F4IntSigmaDelta

momentumLoopTest : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g →
  f4MomentumQuantize s g + f4MomentumResidual s g ≡ f4ExactEMA s g
momentumLoopTest = f4MomentumSigmaDeltaLaw

logLoopTest : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g →
  SigmaDeltaLogStep.fromInt (logStep s) (f4LogQuantum s g) + f4LogResidual s g ≡ f4LogAccumulator s g
logLoopTest = f4LogSigmaDeltaLaw

base2RoundTripTest : ∀ {A : FiniteOrderedRational} (xs : FeatureVec A) →
  idbdLog2 A (idbdPow2 A xs) ≡ xs
base2RoundTripTest = idbdBase2RoundTrip

ffnLayeringTest : ∀ {A : FiniteOrderedRational}
  (f : CanonicalSoftsignSignReLUFFN A) x →
  runCanonicalSoftsignSignReLUFFN f x ≡ runCanonicalSoftsignSignReLUFFN f x
ffnLayeringTest = canonicalFFNLayeringLaw
