{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DPGInt8 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; int8Add; int8Mul)

record GlobalOptimizer : Set where
  constructor globalOptimizer
  field
    stepScale momentum : Int8

record GlobalL2 : Set where
  constructor globalL2
  field
    coefficient : Int8

record DPGState : Set where
  constructor dpgState
  field
    optimizer : GlobalOptimizer
    l2 : GlobalL2
    actorParameter criticParameter : Int8

open DPGState public

actorForward : DPGState → Int8 → Int8
actorForward s x = int8Add (int8Mul (actorParameter s) x) (GlobalL2.coefficient (l2 s))

criticForward : DPGState → Int8 → Int8
criticForward s x = int8Add (int8Mul (criticParameter s) x) (GlobalL2.coefficient (l2 s))

maxBootstrap : Int8 → Int8 → Int8
maxBootstrap q₁ q₂ = q₁

criticTarget : DPGState → Int8 → Int8 → Int8
criticTarget s reward nextQ = int8Add reward (maxBootstrap nextQ (criticForward s reward))

actorTransport : DPGState → Int8 → Int8
actorTransport s x = int8Mul (GlobalOptimizer.stepScale (optimizer s)) x

criticTransport : DPGState → Int8 → Int8
criticTransport s x = int8Mul (GlobalOptimizer.momentum (optimizer s)) x

actorTransport-law : ∀ s x → actorTransport s x ≡ int8Mul (GlobalOptimizer.stepScale (optimizer s)) x
actorTransport-law s x = refl

criticTransport-law : ∀ s x → criticTransport s x ≡ int8Mul (GlobalOptimizer.momentum (optimizer s)) x
criticTransport-law s x = refl

globalL2-actor-law : ∀ s x → actorForward s x ≡ int8Add (int8Mul (actorParameter s) x) (GlobalL2.coefficient (l2 s))
globalL2-actor-law s x = refl

globalL2-critic-law : ∀ s x → criticForward s x ≡ int8Add (int8Mul (criticParameter s) x) (GlobalL2.coefficient (l2 s))
globalL2-critic-law s x = refl
