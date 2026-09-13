{-# OPTIONS --safe #-}
module Exotic.efficient_chad.MobiusSoftsignBridge where

open import Agda.Builtin.Equality using (_≡_; refl; trans; cong; sym)
open import Data.Product using (_,_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; CHADOperator
  ; primal
  ; one8
  ; composeCHAD
  ; composeCHAD-primal
  )
open import Exotic.efficient_chad.MobiusInt8Composition using
  ( FiniteMobiusAction
  ; act
  ; mobiusCompose
  ; mobius-compose-law
  )
open import Exotic.efficient_chad.SoftsignGatedComposition using
  ( SoftsignGatedForward
  ; signReLU8
  ; softsign8
  ; softsignGatedOperator
  )

record ForwardMobiusWitness (op : CHADOperator) : Set₁ where
  constructor forwardMobiusWitness
  field
    action : FiniteMobiusAction
    forward-one : ∀ x →
      act action (x , one8) ≡ (primal op x , one8)

open ForwardMobiusWitness public

composeForwardMobius : ∀ {f g : CHADOperator}
  → ForwardMobiusWitness f
  → ForwardMobiusWitness g
  → ForwardMobiusWitness (composeCHAD g f)
composeForwardMobius wf wg =
  forwardMobiusWitness
    (mobiusCompose (action wg) (action wf))
    witness
  where
    witness : ∀ x →
      act (mobiusCompose (action wg) (action wf)) (x , one8)
      ≡ (primal (composeCHAD g f) x , one8)
    witness x =
      trans
        (mobius-compose-law (action wg) (action wf) (x , one8))
        (trans
          (cong (act (action wg)) (forward-one wf x))
          (trans
            (forward-one wg (primal f x))
            (sym (composeCHAD-primal g f x))))

softsignGatedForwardMobiusWitness : ∀ (f : SoftsignGatedForward)
  → ForwardMobiusWitness (signReLU8 f)
  → ForwardMobiusWitness (softsign8 f)
  → ForwardMobiusWitness (softsignGatedOperator f)
softsignGatedForwardMobiusWitness f signWitness softsignWitness =
  composeForwardMobius signWitness softsignWitness
