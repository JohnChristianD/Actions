{-# OPTIONS --safe #-}

module Exotic.econlib.GameTheory where

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
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

leftBestDefect : ∀ b a' →
  leftScore prisonersDilemma a' b ≤ leftScore prisonersDilemma defect b
leftBestDefect cooperate cooperate = s≤s (s≤s (s≤s z≤n))
leftBestDefect cooperate defect = s≤s z≤n
leftBestDefect defect cooperate = s≤s (s≤s z≤n)
leftBestDefect defect defect = z≤n

rightBestDefect : ∀ a b' →
  rightScore prisonersDilemma a b' ≤ rightScore prisonersDilemma a defect
rightBestDefect cooperate cooperate = s≤s (s≤s (s≤s z≤n))
rightBestDefect cooperate defect = s≤s z≤n
rightBestDefect defect cooperate = s≤s (s≤s z≤n)
rightBestDefect defect defect = z≤n

isNashEquilibriumDD : PureNash prisonersDilemma defect defect
isNashEquilibriumDD = pureNash
  (leftBestDefect defect)
  (rightBestDefect defect)

pdBestResponse : Action → Action
pdBestResponse _ = defect

pdBestResponseFixed : pdBestResponse defect ≡ defect
pdBestResponseFixed = refl

pdStep : Action × Action → Action × Action
pdStep _ = defect , defect

pdStep-stabilises : ∀ s → pdStep s ≡ (defect , defect)
pdStep-stabilises _ = refl

pdIter : ℕ → Action × Action → Action × Action
pdIter zero s = s
pdIter (suc n) s = pdIter n (pdStep s)

pdIter-stabilises : ∀ n s → pdIter (suc n) s ≡ (defect , defect)
pdIter-stabilises zero s = refl
pdIter-stabilises (suc n) s = pdIter-stabilises n (defect , defect)

nashConvergenceWitness : NashCertificate
nashConvergenceWitness = nashCertificate defect defect isNashEquilibriumDD
