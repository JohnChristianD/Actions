{-# OPTIONS --safe #-}
module Exotic.efficient_chad.SoftsignGatedComposition where

open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; CHADOperator
  ; primal
  ; pullback
  ; composeCHAD
  ; composeCHAD-primal
  ; composeCHAD-pullback
  )

-- The finite representation boundary is explicit: signReLU is the forward
-- activation and softsign gates its representation. Concrete operators are
-- supplied by the eventual in-tree activation definitions.
record SoftsignGatedForward : Set₁ where
  constructor softsignGatedForward
  field
    signReLU8 : CHADOperator
    softsign8 : CHADOperator

open SoftsignGatedForward public

softsignGatedOperator : SoftsignGatedForward → CHADOperator
softsignGatedOperator f = composeCHAD (softsign8 f) (signReLU8 f)

softsignGated-primal : ∀ (f : SoftsignGatedForward) (x : Int8)
  → primal (softsignGatedOperator f) x
    ≡ primal (softsign8 f) (primal (signReLU8 f) x)
softsignGated-primal f x =
  composeCHAD-primal (softsign8 f) (signReLU8 f) x

softsignGated-pullback : ∀ (f : SoftsignGatedForward) (x cotangent : Int8)
  → pullback (softsignGatedOperator f) x cotangent
    ≡ pullback (signReLU8 f) x
        (pullback (softsign8 f) (primal (signReLU8 f) x) cotangent)
softsignGated-pullback f x cotangent =
  composeCHAD-pullback (softsign8 f) (signReLU8 f) x cotangent

softsignGatedForwardLaw : Set₁
softsignGatedForwardLaw =
  ∀ (f : SoftsignGatedForward) (x : Int8) →
    primal (softsignGatedOperator f) x
      ≡ primal (softsign8 f) (primal (signReLU8 f) x)

softsignGatedPullbackLaw : Set₁
softsignGatedPullbackLaw =
  ∀ (f : SoftsignGatedForward) (x cotangent : Int8) →
    pullback (softsignGatedOperator f) x cotangent
      ≡ pullback (signReLU8 f) x
          (pullback (softsign8 f) (primal (signReLU8 f) x) cotangent)

softsignGatedForwardLaw-proof : softsignGatedForwardLaw
softsignGatedForwardLaw-proof = softsignGated-primal

softsignGatedPullbackLaw-proof : softsignGatedPullbackLaw
softsignGatedPullbackLaw-proof = softsignGated-pullback

-- A concrete activation-specific Möbius theorem must enter through concrete
-- Int8 activation definitions and their checked Möbius witnesses. The generic
-- composition law above does not fabricate such a witness.
