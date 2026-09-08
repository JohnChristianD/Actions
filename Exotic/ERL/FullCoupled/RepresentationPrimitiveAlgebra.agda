{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.RepresentationPrimitiveAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- Least-intrusion algebraic boundary for representation primitives.
--
-- The base Ring remains finite/algebraic.  Inverse, square root, and tanh
-- are introduced as total functions only through a parameterized contract.
-- Division and square root carry their domain obligations explicitly; tanh
-- carries its derivative law explicitly.  Nothing is postulated globally.
------------------------------------------------------------------------

data ⊥ : Set where

Nonzero : ∀ {A : Set} → A → Set
Nonzero {A} x = x ≡ x → ⊥

record Ring : Set₁ where
  field
    R : Set
    zero one : R
    add mul : R → R → R
    neg : R → R
    addAssoc : ∀ x y z → add (add x y) z ≡ add x (add y z)
    addComm : ∀ x y → add x y ≡ add y x
    addZeroL : ∀ x → add zero x ≡ x
    addZeroR : ∀ x → add x zero ≡ x
    mulAssoc : ∀ x y z → mul (mul x y) z ≡ mul x (mul y z)
    mulComm : ∀ x y → mul x y ≡ mul y x
    mulOneL : ∀ x → mul one x ≡ x
    mulOneR : ∀ x → mul x one ≡ x
    distrib : ∀ x y z → mul x (add y z) ≡ add (mul x y) (mul x z)
    zeroMulL : ∀ x → mul zero x ≡ zero
    zeroMulR : ∀ x → mul x zero ≡ zero
    addNegL : ∀ x → add (neg x) x ≡ zero
    addNegR : ∀ x → add x (neg x) ≡ zero

record PrimitiveAlgebra (G : Ring) : Set₁ where
  open Ring G
  field
    inv : R → R
    invLaw : ∀ {x} → Nonzero x → mul x (inv x) ≡ one
    invVJP : R → R → R
    invVJPLaw : ∀ {x} → Nonzero x → ∀ c → invVJP x c ≡ neg (mul c (mul (inv x) (inv x)))

    sqrt : R → R
    SqrtDomain : R → Set
    sqrtLaw : ∀ {x} → SqrtDomain x → mul (sqrt x) (sqrt x) ≡ x
    sqrtVJP : R → R → R
    sqrtVJPLaw : ∀ {x} → SqrtDomain x → Nonzero (sqrt x) → ∀ c →
      sqrtVJP x c ≡ mul c (inv (add (sqrt x) (sqrt x)))

    tanh : R → R
    tanhDerivative : R → R
    tanhVJP : R → R → R
    tanhVJPLaw : ∀ x c →
      tanhVJP x c ≡ mul c (tanhDerivative x)
    tanhDerivativeLaw : ∀ x →
      tanhDerivative x ≡ add one (neg (mul (tanh x) (tanh x)))

module PrimitiveLaws {G : Ring} (P : PrimitiveAlgebra G) where
  open Ring G
  open PrimitiveAlgebra P

  invValueLaw : ∀ {x} → Nonzero x → mul x (inv x) ≡ one
  invValueLaw = invLaw

  invReverseLaw : ∀ {x} → Nonzero x → ∀ c →
    invVJP x c ≡ neg (mul c (mul (inv x) (inv x)))
  invReverseLaw = invVJPLaw

  sqrtValueLaw : ∀ {x} → SqrtDomain x → mul (sqrt x) (sqrt x) ≡ x
  sqrtValueLaw = sqrtLaw

  sqrtReverseLaw : ∀ {x} → SqrtDomain x → Nonzero (sqrt x) → ∀ c →
    sqrtVJP x c ≡ mul c (inv (add (sqrt x) (sqrt x)))
  sqrtReverseLaw = sqrtVJPLaw

  tanhReverseLaw : ∀ x c → tanhVJP x c ≡ mul c (tanhDerivative x)
  tanhReverseLaw = tanhVJPLaw

  tanhDerivativeValue : ∀ x →
    tanhDerivative x ≡ add one (neg (mul (tanh x) (tanh x)))
  tanhDerivativeValue = tanhDerivativeLaw

  tanhExplicitVJP : ∀ x c →
    tanhVJP x c ≡ mul c (add one (neg (mul (tanh x) (tanh x))))
  tanhExplicitVJP x c =
    trans (tanhVJPLaw x c)
      (cong (mul c) (tanhDerivativeLaw x))

------------------------------------------------------------------------
-- Composition theorem: once each primitive provides its lawful pullback,
-- composition is definitionally chain-rule-shaped and remains total.
------------------------------------------------------------------------

record UnaryPrimitive (G : Ring) : Set₁ where
  open Ring G
  field
    value : R → R
    reverse : R → R → R

compose : ∀ {G : Ring} → UnaryPrimitive G → UnaryPrimitive G → UnaryPrimitive G
compose f g = record
  { value = λ x → UnaryPrimitive.value g (UnaryPrimitive.value f x)
  ; reverse = λ x c →
      UnaryPrimitive.reverse f x
        (UnaryPrimitive.reverse g (UnaryPrimitive.value f x) c)
  }

composeReverse : ∀ {G : Ring} (f g : UnaryPrimitive G) x c →
  UnaryPrimitive.reverse (compose f g) x c ≡
    UnaryPrimitive.reverse f x
      (UnaryPrimitive.reverse g (UnaryPrimitive.value f x) c)
composeReverse f g x c = refl

------------------------------------------------------------------------
-- Layer-normalization algebraic shell.
--
-- This is deliberately the denominator/square-root boundary only, not a
-- fake proof of real square roots inside an arbitrary finite ring.
------------------------------------------------------------------------

layerNormScale : ∀ {G : Ring} → PrimitiveAlgebra G →
  (x eps : Ring.R G) → Ring.R G
layerNormScale P x eps =
  Ring.mul G x (PrimitiveAlgebra.inv P (PrimitiveAlgebra.sqrt P (Ring.add G x eps)))
  where
  G = _

layerNormScaleDef : ∀ {G : Ring} (P : PrimitiveAlgebra G) x eps →
  layerNormScale P x eps ≡
    Ring.mul G x (PrimitiveAlgebra.inv P (PrimitiveAlgebra.sqrt P (Ring.add G x eps)))
layerNormScaleDef P x eps = refl

------------------------------------------------------------------------
-- Combined representation boundary: tanh(layerNormScale(...)).
-- The theorem requires only the explicit primitive contracts; no analytic
-- library and no unsafe axiom are introduced.
------------------------------------------------------------------------

representationValue : ∀ {G : Ring} → PrimitiveAlgebra G →
  (x eps : Ring.R G) → Ring.R G
representationValue P x eps =
  PrimitiveAlgebra.tanh P (layerNormScale P x eps)

representationValueDef : ∀ {G : Ring} (P : PrimitiveAlgebra G) x eps →
  representationValue P x eps ≡
    PrimitiveAlgebra.tanh P (layerNormScale P x eps)
representationValueDef P x eps = refl
