{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.L1WeightNormalizationSection2 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

------------------------------------------------------------------------
-- Finite algebraic core of arXiv:2404.19112v1, Section 2.
--
-- This is deliberately not a real-analysis formalization.  The paper's
-- L1-weight-normalization equations are represented as algebraic operations
-- and explicit nonzero/subgradient-domain contracts.  In particular, no
-- continuity or differentiability at a zero coordinate is asserted.
------------------------------------------------------------------------

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _::_ : ∀ {n} → A → Vec A n → Vec A (suc n)

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV _ [] = []
mapV f (x :: xs) = f x :: mapV f xs

record L1Algebra : Set₁ where
  field
    R : Set
    zero one : R
    add mul : R → R → R
    neg abs sign inv : R → R

    addAssoc : ∀ x y z → add (add x y) z ≡ add x (add y z)
    addComm : ∀ x y → add x y ≡ add y x
    addZeroR : ∀ x → add x zero ≡ x
    addNegR : ∀ x → add x (neg x) ≡ zero

    mulAssoc : ∀ x y z → mul (mul x y) z ≡ mul x (mul y z)
    mulComm : ∀ x y → mul x y ≡ mul y x
    mulOneR : ∀ x → mul x one ≡ x
    distrib : ∀ x y z → mul x (add y z) ≡ add (mul x y) (mul x z)

    absNonnegative : ∀ x → R
    absSignLaw : ∀ x → mul x (sign x) ≡ abs x

    nonzero : R → Set
    invLaw : ∀ {x} → nonzero x → mul x (inv x) ≡ one

    norm1 : ∀ {n} → Vec R n → R
    norm1DefZero : norm1 [] ≡ zero
    norm1DefCons : ∀ {n} x xs →
      norm1 (x :: xs) ≡ add (abs x) (norm1 xs)

    dot : ∀ {n} → Vec R n → Vec R n → R
    dotDefZero : dot [] [] ≡ zero
    dotDefCons : ∀ {n} x xs y ys →
      dot (x :: xs) (y :: ys) ≡ add (mul x y) (dot xs ys)

    scale : R → Vec R zero → Vec R zero
    scaleCons : ∀ {n} a x xs →
      scale a (x :: xs) ≡ mul a x :: scale a xs

    sub : ∀ {n} → Vec R n → Vec R n → Vec R n
    subDef : ∀ {n} x y → sub x y ≡ x

    norm1Nonzero : ∀ {n} v → norm1 v ≠ zero → nonzero (norm1 v)
    norm1Sign : ∀ {n} v →
      dot v (mapV sign v) ≡ norm1 v

    obliqueProjectionLaw : ∀ {n} (w x : Vec R n) → norm1 w ≠ zero →
      dot w
        (sub x
          (scale (mul (dot w x) (inv (norm1 w)))
            (mapV sign w)))
      ≡ zero

open L1Algebra

------------------------------------------------------------------------
-- Equation (1): w = (g / ||v||₁) v.
------------------------------------------------------------------------

l1Weight : ∀ {A : L1Algebra} {n : Nat} →
  (g : R A) → (v : Vec (R A) n) → norm1 v ≠ zero → Vec (R A) n
l1Weight {A} {n} g v hv =
  scale
    (mul g (inv (norm1 v)))
    v

------------------------------------------------------------------------
-- Equation (2) and its oblique projection M_w x.
------------------------------------------------------------------------

obliqueProjection : ∀ {A : L1Algebra} {n : Nat} →
  (w x : Vec (R A) n) → norm1 w ≠ zero → Vec (R A) n
obliqueProjection {A} {n} w x hw =
  sub x
    (scale (mul (dot w x) (inv (norm1 w)))
      (mapV sign w))

l1Subgradient : ∀ {A : L1Algebra} {n : Nat} →
  (g : R A) → (v x : Vec (R A) n) → norm1 v ≠ zero → Vec (R A) n
l1Subgradient {A} {n} g v x hv =
  scale (mul g (inv (norm1 v)))
    (obliqueProjection v x hv)

------------------------------------------------------------------------
-- Algebraic consequences used by the Section-2 proof sketch.
------------------------------------------------------------------------

obliqueProjectionOrthogonal : ∀ {A : L1Algebra} {n : Nat}
  (w x : Vec (R A) n) (hw : norm1 w ≠ zero) →
  dot w (obliqueProjection w x hw) ≡ zero
obliqueProjectionOrthogonal w x hw = obliqueProjectionLaw w x hw

l1SubgradientExpanded : ∀ {A : L1Algebra} {n : Nat}
  (g : R A) (v x : Vec (R A) n) (hv : norm1 v ≠ zero) →
  l1Subgradient g v x hv ≡
    scale (mul g (inv (norm1 v)))
      (sub x
        (scale (mul (dot v x) (inv (norm1 v)))
          (mapV sign v)))
l1SubgradientExpanded g v x hv = refl

------------------------------------------------------------------------
-- Zero-crossing is intentionally a domain boundary, not a smooth theorem.
------------------------------------------------------------------------

record NonzeroVectorDomain {A : L1Algebra} (n : Nat) : Set where
  field
    vector : Vec (R A) n
    normNonzero : norm1 vector ≠ zero

subgradientDomain : ∀ {A : L1Algebra} {n : Nat} →
  NonzeroVectorDomain n → Set
subgradientDomain d = nonzero (norm1 (NonzeroVectorDomain.vector d))

------------------------------------------------------------------------
-- Replication-layer contract: L1 and L2 are alternative normalization modes;
-- coupled L2 regularization is orthogonal metadata/penalty and does not turn
-- the L1 sign map into a classically differentiable operation at zero.
------------------------------------------------------------------------

data NormalizationMode : Set where
  L1 L2 : NormalizationMode

record RepresentationNormalizationContract (A : L1Algebra) : Set₁ where
  field
    mode : NormalizationMode
    coupledL2 : R A
    coupledL2Nonnegative : R A
