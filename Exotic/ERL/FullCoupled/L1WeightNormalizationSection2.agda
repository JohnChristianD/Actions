{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.L1WeightNormalizationSection2 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

data ⊥ : Set where

_≠_ : ∀ {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

------------------------------------------------------------------------
-- Finite algebraic core of arXiv:2404.19112v1, Section 2.
-- No real-analysis infrastructure is used. The L1 normalization and
-- subgradient equations are represented with total algebraic primitives plus
-- explicit nonzero/domain witnesses. No classical differentiability claim
-- is made at a zero coordinate.
------------------------------------------------------------------------

data Vec (A : Set) : Nat → Set where
  [] : Vec A 0
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

    scale : ∀ {n} → R → Vec R n → Vec R n
    scaleCons : ∀ {n} a x xs →
      scale a (x :: xs) ≡ mul a x :: scale a xs

    sub : ∀ {n} → Vec R n → Vec R n → Vec R n

    norm1Nonzero : ∀ {n} v → norm1 v ≠ zero → nonzero (norm1 v)

    norm1Sign : ∀ {n} v →
      dot v (mapV sign v) ≡ norm1 v

    obliqueProjectionLaw : ∀ {n} (w x : Vec R n) → norm1 w ≠ zero →
      dot w
        (sub x
          (scale (mul (dot w x) (inv (norm1 w)))
            (mapV sign w)))
      ≡ zero

------------------------------------------------------------------------
-- Equation (1): w = (g / ||v||₁) v.
------------------------------------------------------------------------

l1Weight : ∀ {A : L1Algebra} {n : Nat} →
  (g : L1Algebra.R A) →
  (v : Vec (L1Algebra.R A) n) →
  L1Algebra.norm1 A v ≠ L1Algebra.zero A →
  Vec (L1Algebra.R A) n
l1Weight {A} g v hv =
  L1Algebra.scale A
    (L1Algebra.mul A g
      (L1Algebra.inv A (L1Algebra.norm1 A v)))
    v

------------------------------------------------------------------------
-- Equation (2) and the oblique projection M_w x.
------------------------------------------------------------------------

obliqueProjection : ∀ {A : L1Algebra} {n : Nat} →
  (w x : Vec (L1Algebra.R A) n) →
  L1Algebra.norm1 A w ≠ L1Algebra.zero A →
  Vec (L1Algebra.R A) n
obliqueProjection {A} w x hw =
  L1Algebra.sub A x
    (L1Algebra.scale A
      (L1Algebra.mul A
        (L1Algebra.dot A w x)
        (L1Algebra.inv A (L1Algebra.norm1 A w)))
      (mapV (L1Algebra.sign A) w))

l1Subgradient : ∀ {A : L1Algebra} {n : Nat} →
  (g : L1Algebra.R A) →
  (v x : Vec (L1Algebra.R A) n) →
  L1Algebra.norm1 A v ≠ L1Algebra.zero A →
  Vec (L1Algebra.R A) n
l1Subgradient {A} g v x hv =
  L1Algebra.scale A
    (L1Algebra.mul A g
      (L1Algebra.inv A (L1Algebra.norm1 A v)))
    (obliqueProjection v x hv)

------------------------------------------------------------------------
-- Algebraic consequences explicitly carried by the Section-2 contract.
------------------------------------------------------------------------

obliqueProjectionOrthogonal : ∀ {A : L1Algebra} {n : Nat}
  (w x : Vec (L1Algebra.R A) n)
  (hw : L1Algebra.norm1 A w ≠ L1Algebra.zero A) →
  L1Algebra.dot A w (obliqueProjection w x hw) ≡ L1Algebra.zero A
obliqueProjectionOrthogonal {A} w x hw =
  L1Algebra.obliqueProjectionLaw A w x hw

l1SubgradientExpanded : ∀ {A : L1Algebra} {n : Nat}
  (g : L1Algebra.R A)
  (v x : Vec (L1Algebra.R A) n)
  (hv : L1Algebra.norm1 A v ≠ L1Algebra.zero A) →
  l1Subgradient g v x hv ≡
    L1Algebra.scale A
      (L1Algebra.mul A g
        (L1Algebra.inv A (L1Algebra.norm1 A v)))
      (L1Algebra.sub A x
        (L1Algebra.scale A
          (L1Algebra.mul A
            (L1Algebra.dot A v x)
            (L1Algebra.inv A (L1Algebra.norm1 A v)))
          (mapV (L1Algebra.sign A) v)))
l1SubgradientExpanded g v x hv = refl

------------------------------------------------------------------------
-- Zero-crossing is intentionally a boundary of the subgradient domain.
------------------------------------------------------------------------

record NonzeroVectorDomain {A : L1Algebra} (n : Nat) : Set where
  field
    vector : Vec (L1Algebra.R A) n
    normNonzero : L1Algebra.norm1 A vector ≠ L1Algebra.zero A

subgradientDomain : ∀ {A : L1Algebra} {n : Nat} →
  NonzeroVectorDomain n → Set
subgradientDomain {A} d =
  L1Algebra.nonzero A
    (L1Algebra.norm1 A (NonzeroVectorDomain.vector d))

------------------------------------------------------------------------
-- Representation-layer contract: L1 and L2 are alternative normalization
-- variants; coupled L2 regularization is an independent algebraic parameter.
------------------------------------------------------------------------

data NormalizationMode : Set where
  L1 L2 : NormalizationMode

record RepresentationNormalizationContract (A : L1Algebra) : Set₁ where
  field
    mode : NormalizationMode
    coupledL2 : L1Algebra.R A
