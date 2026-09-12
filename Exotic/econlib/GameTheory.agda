{-# OPTIONS --safe #-}

module Exotic.econlib.GameTheory where

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; code)

data Action : Set where
  cooperate : Action
  defect : Action

record Game2 : Set₁ where
  constructor game2
  field
    payoff : Action → Action → Int8 × Int8

open Game2 public

leftPayoff : Game2 → Action → Action → Int8
leftPayoff G a b = proj₁ (payoff G a b)

rightPayoff : Game2 → Action → Action → Int8
rightPayoff G a b = proj₂ (payoff G a b)

leftScore : Game2 → Action → Action → ℕ
leftScore G a b = toℕ (code (leftPayoff G a b))

rightScore : Game2 → Action → Action → ℕ
rightScore G a b = toℕ (code (rightPayoff G a b))

record PureNash (G : Game2) (a b : Action) : Set where
  constructor pureNash
  field
    leftBest : ∀ a' → leftScore G a' b ≤ leftScore G a b
    rightBest : ∀ b' → rightScore G a b' ≤ rightScore G a b

prisonersDilemma : Game2
prisonersDilemma = game2 λ where
  cooperate cooperate = int8OfNat 3 , int8OfNat 3
  cooperate defect    = int8OfNat 0 , int8OfNat 5
  defect    cooperate = int8OfNat 5 , int8OfNat 0
  defect    defect    = int8OfNat 1 , int8OfNat 1

record NashCertificate : Set where
  constructor nashCertificate
  field
    action₁ action₂ : Action
    witness : PureNash prisonersDilemma action₁ action₂

nashCertificateIdentity : ∀ {a b} → PureNash prisonersDilemma a b →
  PureNash prisonersDilemma a b
nashCertificateIdentity w = w
