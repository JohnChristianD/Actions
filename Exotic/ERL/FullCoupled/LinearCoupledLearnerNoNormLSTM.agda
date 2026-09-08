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
    addR mulR : R → R → R
    neg : R → R
    addAssoc : ∀ x y z → addR (addR x y) z ≡ addR x (addR y z)
    addComm : ∀ x y → addR x y ≡ addR y x
    addZeroL : ∀ x → addR zero x ≡ x
    addZeroR : ∀ x → addR x zero ≡ x
    mulAssoc : ∀ x y z → mulR (mulR x y) z ≡ mulR x (mulR y z)
    mulComm : ∀ x y → mulR x y ≡ mulR y x
    mulOneL : ∀ x → mulR one x ≡ x
    mulOneR : ∀ x → mulR x one ≡ x
    distrib : ∀ x y z → mulR x (addR y z) ≡ addR (mulR x y) (mulR x z)
    zeroMulL : ∀ x → mulR zero x ≡ zero
    zeroMulR : ∀ x → mulR x zero ≡ zero

module Learner (A : Ring) (n : Nat) where
  open Ring A

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
  scale a v = map (λ x → mulR a x) v

  add : ∀ {m} → Vec m → Vec m → Vec m
  add = zipWith addR

  dot : ∀ {m} → Vec m → Vec m → R
  dot [] [] = zero
  dot (x ∷ xs) (y ∷ ys) = addR (mulR x y) (dot xs ys)

  linearQ : Vec n → Vec n → R
  linearQ w φ = dot w φ

  tdError : R → R → R
  tdError target q = addR target (neg q)

  l2Decay : R → Vec n → Vec n
  l2Decay rho w = scale (addR one (neg rho)) w

  criticUpdate : R → R → Vec n → Vec n → Vec n
  criticUpdate alpha delta w φ =
    add w (scale (mulR alpha delta) φ)

  coupledUpdate : R → R → R → Vec n → Vec n → Vec n
  coupledUpdate alpha delta rho w φ =
    l2Decay rho (criticUpdate alpha delta w φ)

  learnerStep : R → R → R → Vec n → Vec n → Vec n
  learnerStep alpha target rho w φ =
    coupledUpdate alpha (tdError target (linearQ w φ)) rho w φ

  exploreScore : R → R → R → R
  exploreScore q bonus epsilon = addR q (mulR epsilon bonus)

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
      add w (scale (mulR alpha delta) φ)
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
    exploreScore q bonus epsilon ≡ addR q (mulR epsilon bonus)
  explorationScoreExpanded q bonus epsilon = refl

  explorationVectorExpanded :
    ∀ epsilon q bonus →
    exploreVector epsilon q bonus ≡ add q (scale epsilon bonus)
  explorationVectorExpanded epsilon q bonus = refl

------------------------------------------------------------------------
-- Authoritative CI retrigger: learner source is unchanged semantically.
------------------------------------------------------------------------
