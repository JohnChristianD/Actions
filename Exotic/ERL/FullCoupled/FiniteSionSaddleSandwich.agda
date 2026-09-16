{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.FiniteSionSaddleSandwich where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)

record OrderedCarrier : Set₁ where
  constructor orderedCarrier
  field
    Carrier : Set
    _≤_ : Carrier → Carrier → Set
    refl≤ : ∀ x → _≤_ x x
    trans≤ : ∀ {x y z} → _≤_ x y → _≤_ y z → _≤_ x z
open OrderedCarrier public

record SaddlePoint
  (X Y Z : OrderedCarrier)
  (payoff : Carrier X → Carrier Y → Carrier Z) : Set₁ where
  constructor saddlePoint
  field
    xStar : Carrier X
    yStar : Carrier Y
    leftSaddle : ∀ x → _≤_ Z (payoff x yStar) (payoff xStar yStar)
    rightSaddle : ∀ y → _≤_ Z (payoff xStar yStar) (payoff xStar y)
open SaddlePoint public

record FiniteSionWitness
  (X Y Z : OrderedCarrier)
  (payoff : Carrier X → Carrier Y → Carrier Z) : Set₁ where
  constructor finiteSionWitness
  field
    saddle : SaddlePoint X Y Z payoff
    leftEnvelope : Carrier X → Carrier Z
    rightEnvelope : Carrier Y → Carrier Z
    leftEnvelope-law : ∀ x → leftEnvelope x ≡ payoff x (yStar saddle)
    rightEnvelope-law : ∀ y → rightEnvelope y ≡ payoff (xStar saddle) y
open FiniteSionWitness public

finiteSionSandwich :
  ∀ {X Y Z : OrderedCarrier}
    {payoff : Carrier X → Carrier Y → Carrier Z}
    (W : FiniteSionWitness X Y Z payoff) →
    _≤_ Z
      (payoff (xStar (saddle W)) (yStar (saddle W)))
      (payoff (xStar (saddle W)) (yStar (saddle W)))
finiteSionSandwich W = refl≤ Z (payoff (xStar (saddle W)) (yStar (saddle W)))

finiteSion-left-envelope :
  ∀ {X Y Z : OrderedCarrier}
    {payoff : Carrier X → Carrier Y → Carrier Z}
    (W : FiniteSionWitness X Y Z payoff) (x : Carrier X) →
    _≤_ Z
      (leftEnvelope W x)
      (payoff (xStar (saddle W)) (yStar (saddle W)))
finiteSion-left-envelope W x =
  subst
    (λ z → _≤_ Z z (payoff (xStar (saddle W)) (yStar (saddle W))))
    (leftEnvelope-law W x)
    (leftSaddle (saddle W) x)

finiteSion-right-envelope :
  ∀ {X Y Z : OrderedCarrier}
    {payoff : Carrier X → Carrier Y → Carrier Z}
    (W : FiniteSionWitness X Y Z payoff) (y : Carrier Y) →
    _≤_ Z
      (payoff (xStar (saddle W)) (yStar (saddle W)))
      (rightEnvelope W y)
finiteSion-right-envelope W y =
  subst
    (λ z → _≤_ Z (payoff (xStar (saddle W)) (yStar (saddle W))) z)
    (rightEnvelope-law W y)
    (rightSaddle (saddle W) y)

natOrderedCarrier : OrderedCarrier
natOrderedCarrier = orderedCarrier Nat _≤_ natLe-refl natLe-trans
  where
    natLe-refl : ∀ n → n ≤ n
    natLe-refl zero = z≤n
    natLe-refl (suc n) = s≤s (natLe-refl n)

    natLe-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    natLe-trans z≤n _ = z≤n
    natLe-trans (s≤s p) (s≤s q) = s≤s (natLe-trans p q)

finiteSion-nat-self-sandwich :
  ∀ {X Y : OrderedCarrier}
    {payoff : Carrier X → Carrier Y → Nat}
    (W : FiniteSionWitness X Y natOrderedCarrier payoff) →
    payoff (xStar (saddle W)) (yStar (saddle W)) ≡
    payoff (xStar (saddle W)) (yStar (saddle W))
finiteSion-nat-self-sandwich W = refl

-- This is deliberately the finite saddle-point specialization of the Sion
-- sandwich. It proves only what follows from the explicit finite witness;
-- no topological compactness, real-vector convexity, or minimax theorem is
-- imported into the learner kernel.
