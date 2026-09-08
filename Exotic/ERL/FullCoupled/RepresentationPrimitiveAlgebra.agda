{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.RepresentationPrimitiveAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl)

data ⊥ : Set where

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

------------------------------------------------------------------------
-- Minimal total algebraic boundary for representation primitives.
-- Domain side conditions are carried as data, so --safe remains intact.
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
    nonzeroLaw : ∀ x → Nonzero x → x ≡ zero → ⊥

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

    sigmoid : R → R
    sigmoidDerivative : R → R
    sigmoidVJP : R → R → R
    sigmoidVJPLaw : ∀ x c →
      sigmoidVJP x c ≡ mul c (sigmoidDerivative x)
    sigmoidDerivativeLaw : ∀ x →
      sigmoidDerivative x ≡
        mul (sigmoid x) (add one (neg (sigmoid x)))

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

  sigmoidReverseLaw : ∀ x c →
    sigmoidVJP x c ≡ mul c (sigmoidDerivative x)
  sigmoidReverseLaw = sigmoidVJPLaw

  sigmoidDerivativeValue : ∀ x →
    sigmoidDerivative x ≡
      mul (sigmoid x) (add one (neg (sigmoid x)))
  sigmoidDerivativeValue = sigmoidDerivativeLaw

  sigmoidExplicitVJP : ∀ x c →
    sigmoidVJP x c ≡
      mul c (mul (sigmoid x) (add one (neg (sigmoid x))))
  sigmoidExplicitVJP x c =
    trans (sigmoidVJPLaw x c)
      (cong (mul c) (sigmoidDerivativeLaw x))

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

  record SafeInvSqrt (x : R) : Set where
    field
      rootDomain : SqrtDomain x
      rootNonzero : Nonzero (sqrt x)

  invSqrt : R → R
  invSqrt x = inv (sqrt x)

  invSqrtDef : ∀ x →
    invSqrt x ≡ inv (sqrt x)
  invSqrtDef x = refl

  invSqrtBack : R → R → R
  invSqrtBack x c = sqrtVJP x (invVJP (sqrt x) c)

  invSqrtVJPChain : ∀ {x} → SqrtDomain x → Nonzero (sqrt x) → ∀ c →
    invSqrtBack x c ≡ sqrtVJP x (invVJP (sqrt x) c)
  invSqrtVJPChain _ _ c = refl

  invSqrtSafeVJPChain : ∀ {x} → SafeInvSqrt x → ∀ c →
    invSqrtBack x c ≡
      sqrtVJP x (invVJP (sqrt x) c)
  invSqrtSafeVJPChain d c =
    invSqrtVJPChain
      (SafeInvSqrt.rootDomain d)
      (SafeInvSqrt.rootNonzero d)
      c

  scale : R → R → R
  scale x eps = mul x (invSqrt (add x eps))

  scaleDef : ∀ x eps →
    scale x eps ≡ mul x (inv (sqrt (add x eps)))
  scaleDef x eps = refl

  normalizedValue : R → R → R
  normalizedValue x eps = tanh (scale x eps)

  normalizedValueDef : ∀ x eps →
    normalizedValue x eps ≡ tanh (scale x eps)
  normalizedValueDef x eps = refl

  normalizedPrimitiveChain : ∀ x eps c →
    tanhVJP (scale x eps) c ≡
      mul c (tanhDerivative (scale x eps))
  normalizedPrimitiveChain x eps c = tanhVJPLaw (scale x eps) c

  normalizedPrimitiveExplicit : ∀ x eps c →
    tanhVJP (scale x eps) c ≡
      mul c (add one
        (neg (mul (tanh (scale x eps)) (tanh (scale x eps)))))
  normalizedPrimitiveExplicit x eps c =
    trans
      (normalizedPrimitiveChain x eps c)
      (cong (mul c) (tanhDerivativeLaw (scale x eps)))

------------------------------------------------------------------------
-- Combined representation boundary.
------------------------------------------------------------------------

representationBoundary : ∀ {G : Ring} → PrimitiveAlgebra G →
  Ring.R G → Ring.R G → Ring.R G
representationBoundary P x eps = LayerNorm.normalizedValue P x eps

representationBoundaryDef : ∀ {G : Ring} (P : PrimitiveAlgebra G) x eps →
  representationBoundary P x eps ≡
    PrimitiveAlgebra.tanh P (LayerNorm.scale P x eps)
representationBoundaryDef P x eps = refl

representationBoundaryPrimitiveExplicit :
  ∀ {G : Ring} (P : PrimitiveAlgebra G) x eps c →
  PrimitiveAlgebra.tanhVJP P (LayerNorm.scale P x eps) c ≡
    Ring.mul G c
      (Ring.add G (Ring.one G)
        (Ring.neg G
          (Ring.mul G
            (PrimitiveAlgebra.tanh P (LayerNorm.scale P x eps))
            (PrimitiveAlgebra.tanh P (LayerNorm.scale P x eps)))))
representationBoundaryPrimitiveExplicit P x eps c =
  LayerNorm.normalizedPrimitiveExplicit P x eps c