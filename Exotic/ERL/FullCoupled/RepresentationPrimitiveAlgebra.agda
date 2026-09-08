{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.RepresentationPrimitiveAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl; trans; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data ⊥ : Set where

------------------------------------------------------------------------
-- Minimal total algebraic boundary for representation primitives.
------------------------------------------------------------------------

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
    Nonzero : R → Set
    NonzeroDef : ∀ {x} → Nonzero x ≡ (x ≡ zero → ⊥)

    inv : R → R
    invLaw : ∀ {x} → Nonzero x → mul x (inv x) ≡ one
    invVJP : R → R → R
    invVJPLaw : ∀ {x} → Nonzero x → ∀ c →
      invVJP x c ≡ neg (mul c (mul (inv x) (inv x)))

    SqrtDomain : R → Set
    sqrt : R → R
    sqrtLaw : ∀ {x} → SqrtDomain x → mul (sqrt x) (sqrt x) ≡ x
    sqrtVJP : R → R → R
    sqrtVJPLaw : ∀ {x} → SqrtDomain x → Nonzero (sqrt x) → ∀ c →
      sqrtVJP x c ≡ mul c (inv (add (sqrt x) (sqrt x)))

    tanh : R → R
    tanhDerivative : R → R
    tanhVJP : R → R → R
    tanhVJPLaw : ∀ x c → tanhVJP x c ≡ mul c (tanhDerivative x)
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
-- Purely algebraic primitive-node composition.
------------------------------------------------------------------------

record UnaryPrimitive (G : Ring) : Set₁ where
  field
    value : Ring.R G → Ring.R G
    reverse : Ring.R G → Ring.R G → Ring.R G

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
-- Layer-normalization denominator boundary.
------------------------------------------------------------------------

module LayerNorm {G : Ring} (P : PrimitiveAlgebra G) where
  open Ring G
  open PrimitiveAlgebra P

  scale : R → R → R
  scale x eps = mul x (inv (sqrt (add x eps)))

  scaleDef : ∀ x eps →
    scale x eps ≡ mul x (inv (sqrt (add x eps)))
  scaleDef x eps = refl

  normalizedValue : R → R → R
  normalizedValue x eps = tanh (scale x eps)

  normalizedValueDef : ∀ x eps →
    normalizedValue x eps ≡ tanh (scale x eps)
  normalizedValueDef x eps = refl

------------------------------------------------------------------------
-- The combined representation boundary is kernel-visible without requiring
-- a real-analysis library.  Concrete real/rational models instantiate the
-- PrimitiveAlgebra contract; finite test oracles validate their chosen laws.
------------------------------------------------------------------------

representationBoundary : ∀ {G : Ring} → PrimitiveAlgebra G →
  Ring.R G → Ring.R G → Ring.R G
representationBoundary P x eps = LayerNorm.normalizedValue P x eps

representationBoundaryDef : ∀ {G : Ring} (P : PrimitiveAlgebra G) x eps →
  representationBoundary P x eps ≡
    PrimitiveAlgebra.tanh P (LayerNorm.scale P x eps)
representationBoundaryDef P x eps = refl
