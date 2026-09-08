{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.LinearCoupledLearnerNoNormLSTM where

import Agda.Builtin.Nat as NatB
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Isolated learner surface.
-- No LSTM, no normalization, no CHAD dependency, no floating point.
------------------------------------------------------------------------

record Ring : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg : R → R
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    addComm : ∀ x y → x + y ≡ y + x
    addZeroL : ∀ x → zero + x ≡ x
    addZeroR : ∀ x → x + zero ≡ x
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    mulComm : ∀ x y → x * y ≡ y * x
    mulOneL : ∀ x → one * x ≡ x
    mulOneR : ∀ x → x * one ≡ x
    distrib : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    zeroMulL : ∀ x → zero * x ≡ zero
    zeroMulR : ∀ x → x * zero ≡ zero

module Learner (A : Ring) (n : Nat) where
  open Ring A

  infixl 6 _+_
  infixl 7 _*_

  data Vec : Nat → Set where
    [] : Vec NatB.zero
    _∷_ : ∀ {m} → R → Vec m → Vec (suc m)

  map : ∀ {m} → (R → R) → Vec m → Vec m
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  zipWith : ∀ {m} → (R → R → R) → Vec m → Vec m → Vec m
  zipWith f [] [] = []
  zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

  scale : ∀ {m} → R → Vec m → Vec m
  scale a v = map (λ x → a * x) v

  add : ∀ {m} → Vec m → Vec m → Vec m
  add = zipWith _+_

  dot : ∀ {m} → Vec m → Vec m → R
  dot [] [] = zero
  dot (x ∷ xs) (y ∷ ys) = x * y + dot xs ys

  linearQ : Vec n → Vec n → R
  linearQ w φ = dot w φ

  tdError : R → R → R
  tdError target q = target + neg q

  l2Decay : R → Vec n → Vec n
  l2Decay rho w = scale (one + neg rho) w

  criticUpdate : R → R → Vec n → Vec n → Vec n
  criticUpdate alpha delta w φ =
    add w (scale (alpha * delta) φ)

  coupledUpdate : R → R → R → Vec n → Vec n → Vec n
  coupledUpdate alpha delta rho w φ =
    l2Decay rho (criticUpdate alpha delta w φ)

  learnerStep : R → R → R → Vec n → Vec n → Vec n
  learnerStep alpha target rho w φ =
    coupledUpdate alpha (tdError target (linearQ w φ)) rho w φ

  exploreScore : R → R → R → R
  exploreScore q bonus epsilon = q + epsilon * bonus

  exploreVector : R → Vec n → Vec n → Vec n
  exploreVector epsilon q bonus =
    add q (scale epsilon bonus)

  ----------------------------------------------------------------------
  -- Exact definitional certificates. These intentionally isolate the
  -- learner meat from the recurrent/CHAD theorem surface.
  ----------------------------------------------------------------------

  criticUpdateExpanded :
    ∀ alpha delta w φ →
    criticUpdate alpha delta w φ ≡
      add w (scale (alpha * delta) φ)
  criticUpdateExpanded alpha delta w φ = refl

  coupledUpdateExpanded :
    ∀ alpha delta rho w φ →
    coupledUpdate alpha delta rho w φ ≡
      l2Decay rho (criticUpdate alpha delta w φ)
  coupledUpdateExpanded alpha delta rho w φ = refl

  learnerStepExpanded :
    ∀ alpha target rho w φ →
    learnerStep alpha target rho w φ ≡
      coupledUpdate alpha (tdError target (linearQ w φ)) rho w φ
  learnerStepExpanded alpha target rho w φ = refl

  explorationScoreExpanded :
    ∀ q bonus epsilon →
    exploreScore q bonus epsilon ≡ q + epsilon * bonus
  explorationScoreExpanded q bonus epsilon = refl

  explorationVectorExpanded :
    ∀ epsilon q bonus →
    exploreVector epsilon q bonus ≡ add q (scale epsilon bonus)
  explorationVectorExpanded epsilon q bonus = refl
