{-# OPTIONS --safe #-}
module Exotic.efficient_chad.MobiusSoftsignBridge where

open import Agda.Builtin.Equality using (_≡_; trans; cong; sym)
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

record PointwiseForwardMobiusWitness (op : CHADOperator) : Set₁ where
  constructor pointwiseForwardMobiusWitness
  field
    action : Int8 → FiniteMobiusAction
    forward-one : ∀ x →
      act (action x) (x , one8) ≡ (primal op x , one8)

open PointwiseForwardMobiusWitness public

composePointwiseForwardMobius : ∀ {f g : CHADOperator}
  → PointwiseForwardMobiusWitness f
  → PointwiseForwardMobiusWitness g
  → PointwiseForwardMobiusWitness (composeCHAD g f)
composePointwiseForwardMobius wf wg =
  pointwiseForwardMobiusWitness
    (λ x → mobiusCompose (action wg (primal f x)) (action wf x))
    witness
  where
    witness : ∀ x →
      act
        (mobiusCompose (action wg (primal f x)) (action wf x))
        (x , one8)
      ≡ (primal (composeCHAD g f) x , one8)
    witness x =
      trans
        (mobius-compose-law
          (action wg (primal f x))
          (action wf x)
          (x , one8))
        (trans
          (cong
            (act (action wg (primal f x)))
            (forward-one wf x))
          (trans
            (forward-one wg (primal f x))
            (sym (composeCHAD-primal g f x))))

softsignGatedForwardMobiusWitness : ∀ (f : SoftsignGatedForward)
  → PointwiseForwardMobiusWitness (signReLU8 f)
  → PointwiseForwardMobiusWitness (softsign8 f)
  → PointwiseForwardMobiusWitness (softsignGatedOperator f)
softsignGatedForwardMobiusWitness f signWitness softsignWitness =
  composePointwiseForwardMobius signWitness softsignWitness

-- The composition theorem is pointwise in the forward signReLU output. A
-- concrete Möbius certificate for the actual Int8 activation must still
-- provide the pointwise witnesses for signReLU8 and softsign8.
