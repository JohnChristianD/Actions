{-# OPTIONS --safe #-}
module Exotic.efficient_chad.SoftsignGatedComposition where

open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; CHADOperator
  ; primal
  ; composeCHAD
  ; composeCHAD-primal
  )

-- The forward representation boundary is deliberately explicit:
-- signReLU is the forward activation, and softsign is the gate applied to
-- its representation. Concrete activation-specific laws are supplied by
-- their operators rather than being fabricated here.
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

-- Any activation-specific Möbius theorem must enter through the concrete
-- signReLU8/softsign8 operators. Composition itself is kernel-checked here.
record MobiusLaw : Set₁ where
  constructor mobiusLaw
  field
    operator : CHADOperator
    mobiusWitness : Set

open MobiusLaw public

composeMobiusLaw : (outer inner : MobiusLaw) → MobiusLaw
composeMobiusLaw outer inner =
  mobiusLaw
    (composeCHAD (operator outer) (operator inner))
    (mobiusWitness outer)
