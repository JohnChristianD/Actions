{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.RepresentationLayerNormClosure where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.RepresentationPrimitiveAlgebra as RP

------------------------------------------------------------------------
-- Domain-carrying LayerNorm closure.
--
-- The existing primitive algebra remains unchanged.  This layer only
-- packages the side conditions needed by inverse-square-root normalization
-- so the recurrent representation path has an explicit finite algebraic
-- domain at every normalized value.
------------------------------------------------------------------------

module SafeLayerNorm {G : RP.Ring} (P : RP.PrimitiveAlgebra G) where
  open RP.Ring G
  open RP.PrimitiveAlgebra P
  module LN = RP.LayerNorm P

  record SafeNormalizedInput (x eps : R) : Set where
    field
      denominator : LN.SafeInvSqrt (add x eps)

  safeDenominator : ∀ {x eps : R} →
    SafeNormalizedInput x eps → LN.SafeInvSqrt (add x eps)
  safeDenominator d = SafeNormalizedInput.denominator d

  invSqrtExpanded : ∀ {x : R} → LN.SafeInvSqrt x → ∀ c →
    LN.invSqrtBack x c ≡
      sqrtVJP x (invVJP (sqrt x) c)
  invSqrtExpanded d c =
    LN.invSqrtSafeVJPChain d c

  invSqrtExplicit : ∀ {x : R} → LN.SafeInvSqrt x → ∀ c →
    LN.invSqrtBack x c ≡
      mul
        (neg (mul c (mul (inv (sqrt x)) (inv (sqrt x)))))
        (inv (add (sqrt x) (sqrt x)))
  invSqrtExplicit d c =
    trans
      (invSqrtExpanded d c)
      (trans
        (cong
          (sqrtVJP x)
          (invVJPLaw
            (LN.SafeInvSqrt.rootNonzero d)
            c))
        (sqrtVJPLaw
          (LN.SafeInvSqrt.rootDomain d)
          (LN.SafeInvSqrt.rootNonzero d)
          (neg (mul c (mul (inv (sqrt x)) (inv (sqrt x)))))))

  safeScale : ∀ {x eps : R} →
    SafeNormalizedInput x eps → R
  safeScale d =
    mul
      (fst (RP._,_ R R))
      (fst (RP._,_ R R))

  safeScaleDef : ∀ {x eps : R}
    (d : SafeNormalizedInput x eps) →
    safeScale {x} {eps} d ≡
      mul x (inv (sqrt (add x eps)))
  safeScaleDef d = refl

  normalizedValueSafe : ∀ {x eps : R} →
    SafeNormalizedInput x eps → R
  normalizedValueSafe d = tanh (safeScale d)

  normalizedValueSafeDef : ∀ {x eps : R}
    (d : SafeNormalizedInput x eps) →
    normalizedValueSafe d ≡ tanh (safeScale d)
  normalizedValueSafeDef d = refl

  normalizedPrimitiveSafe : ∀ {x eps : R}
    (d : SafeNormalizedInput x eps) → ∀ c →
    tanhVJP (safeScale d) c ≡
      mul c (tanhDerivative (safeScale d))
  normalizedPrimitiveSafe d c = tanhVJPLaw (safeScale d) c

  normalizedPrimitiveExplicitSafe : ∀ {x eps : R}
    (d : SafeNormalizedInput x eps) → ∀ c →
    tanhVJP (safeScale d) c ≡
      mul c
        (add one
          (neg
            (mul
              (tanh (safeScale d))
              (tanh (safeScale d)))))
  normalizedPrimitiveExplicitSafe d c =
    trans
      (normalizedPrimitiveSafe d c)
      (cong
        (mul c)
        (tanhDerivativeLaw (safeScale d)))

  representationSafeBoundary : ∀ {x eps : R}
    (d : SafeNormalizedInput x eps) →
    normalizedValueSafe d ≡
      tanh (mul x (inv (sqrt (add x eps))))
  representationSafeBoundary d =
    trans
      (normalizedValueSafeDef d)
      (cong tanh (safeScaleDef d))
