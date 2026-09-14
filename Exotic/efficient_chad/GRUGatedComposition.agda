{-# OPTIONS --safe #-}
module Exotic.efficient_chad.GRUGatedComposition where

open import Agda.Builtin.Equality using (_≡_; refl; trans; cong; sym)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; CHADOperator
  ; primal
  ; pullback
  ; one8
  ; composeCHAD
  ; composeCHAD-primal
  ; composeCHAD-pullback
  ; affineCHADOperator
  ; affineCHAD
  )
open import Exotic.efficient_chad.MobiusInt8Composition using
  ( FiniteMobiusAction
  ; act
  ; mobiusCompose
  ; mobius-compose-law
  )

-- The only nonlinear maps retained in the recurrent boundary are internal
-- GRU nonlinearities. No standalone forward MLP or pointwise activation layer
-- is part of this interface.
record GRUActivations : Set₁ where
  constructor gruActivations
  field
    signReLU8 : CHADOperator
    softsign8 : CHADOperator
    half8 : CHADOperator

open GRUActivations public

onePlus8 : CHADOperator
onePlus8 = affineCHADOperator (affineCHAD one8 one8)

onePlusSoftsign8 : GRUActivations → CHADOperator
onePlusSoftsign8 a = composeCHAD onePlus8 (softsign8 a)

sigmoidLike8 : GRUActivations → CHADOperator
sigmoidLike8 a = composeCHAD (half8 a) (onePlusSoftsign8 a)

sigmoidLike8-primal : ∀ (a : GRUActivations) (x : Int8)
  → primal (sigmoidLike8 a) x
    ≡ primal (half8 a)
        (primal (onePlus8) (primal (softsign8 a) x))
sigmoidLike8-primal a x =
  trans
    (composeCHAD-primal (half8 a) (onePlusSoftsign8 a) x)
    (cong (primal (half8 a)) (composeCHAD-primal onePlus8 (softsign8 a) x))

sigmoidLike8-pullback : ∀ (a : GRUActivations) (x cotangent : Int8)
  → pullback (sigmoidLike8 a) x cotangent
    ≡ pullback (softsign8 a) x
        (pullback onePlus8 (primal (softsign8 a) x)
          (pullback (half8 a)
            (primal (onePlusSoftsign8 a) x) cotangent))
sigmoidLike8-pullback a x cotangent =
  trans
    (composeCHAD-pullback (half8 a) (onePlusSoftsign8 a) x cotangent)
    (cong
      (λ q → pullback (softsign8 a) x
        (pullback onePlus8 (primal (softsign8 a) x) q))
      refl)

record GRUSequentialBoundary : Set₁ where
  constructor gruSequentialBoundary
  field
    activations : GRUActivations

open GRUSequentialBoundary public

gruCandidate8 : GRUSequentialBoundary → CHADOperator
gruCandidate8 g = signReLU8 (activations g)

gruUpdate8 : GRUSequentialBoundary → CHADOperator
gruUpdate8 g = sigmoidLike8 (activations g)

gruReset8 : GRUSequentialBoundary → CHADOperator
gruReset8 g = sigmoidLike8 (activations g)

-- Möbius closure is conditional on concrete finite witnesses for the actual
-- internal operators. The witness is pointwise because the outer GRU gate is
-- evaluated at the output of the inner finite map.
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

sigmoidLike8MobiusWitness : ∀ (g : GRUSequentialBoundary)
  → PointwiseForwardMobiusWitness (half8 (activations g))
  → PointwiseForwardMobiusWitness (softsign8 (activations g))
  → PointwiseForwardMobiusWitness (sigmoidLike8 g)
sigmoidLike8MobiusWitness g halfWitness softsignWitness =
  composePointwiseForwardMobius halfWitness
    (composePointwiseForwardMobius
      (pointwiseForwardMobiusWitness
        (λ x → pointwise-one-plus)
        (λ x → refl))
      softsignWitness)
  where
    pointwise-one-plus : FiniteMobiusAction
    pointwise-one-plus =
      mobiusCompose
        (pointwiseForwardMobiusWitness.action halfWitness one8)
        (pointwiseForwardMobiusWitness.action softsignWitness one8)
