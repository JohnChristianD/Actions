{-# OPTIONS --safe #-}

module Exotic.econlib.GameTheory where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

record Int8 : Set where
  constructor int8
  field code : Fin 256
open Int8 public

int8OfNat : Nat → Int8
int8OfNat n = int8 (fromℕ< (m%n<n n 256))

int8Roundtrip : ∀ x → toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
int8Roundtrip x =
  let b = toℕ (code x) in
  trans (toℕ-fromℕ< (m%n<n b 256)) (m<n⇒m%n≡m (toℕ<n b))

data Action : Set where
  cooperate : Action
  defect : Action

record Game2 : Set₁ where
  constructor game2
  field
    payoff : Action → Action → Int8 × Int8

open Game2 public

leftPayoff : Game2 → Action → Action → Int8
leftPayoff G a b with payoff G a b
... | p , q = p

rightPayoff : Game2 → Action → Action → Int8
rightPayoff G a b with payoff G a b
... | p , q = q

leftScore : Game2 → Action → Action → Nat
leftScore G a b = toℕ (code (leftPayoff G a b))

rightScore : Game2 → Action → Action → Nat
rightScore G a b = toℕ (code (rightPayoff G a b))

record PureNash (G : Game2) (a b : Action) : Set where
  constructor pureNash
  field
    leftBest : ∀ a' → leftScore G a' b ≤ leftScore G a b
    rightBest : ∀ b' → rightScore G a b' ≤ rightScore G a b

prisonersDilemma : Game2
prisonersDilemma = game2 λ where
  cooperate cooperate → (int8OfNat 3 , int8OfNat 3)
  cooperate defect    → (int8OfNat 0 , int8OfNat 5)
  defect    cooperate → (int8OfNat 5 , int8OfNat 0)
  defect    defect    → (int8OfNat 1 , int8OfNat 1)

record NashCertificate : Set where
  constructor nashCertificate
  field
    action₁ action₂ : Action
    witness : PureNash prisonersDilemma action₁ action₂

nashCertificateIdentity : ∀ {a b} → PureNash prisonersDilemma a b → PureNash prisonersDilemma a b
nashCertificateIdentity w = w

natSelfLe : ∀ n → n ≤ n
natSelfLe zero = z≤n
natSelfLe (suc n) = s≤s (natSelfLe n)

leftBestDefect : ∀ b a' → leftScore prisonersDilemma a' b ≤ leftScore prisonersDilemma defect b
leftBestDefect cooperate cooperate = s≤s (s≤s (s≤s z≤n))
leftBestDefect cooperate defect = natSelfLe 5
leftBestDefect defect cooperate = z≤n
leftBestDefect defect defect = natSelfLe 1

rightBestDefect : ∀ a b' → rightScore prisonersDilemma a b' ≤ rightScore prisonersDilemma a defect
rightBestDefect cooperate cooperate = s≤s (s≤s (s≤s z≤n))
rightBestDefect cooperate defect = natSelfLe 5
rightBestDefect defect cooperate = z≤n
rightBestDefect defect defect = natSelfLe 1

isNashEquilibriumDD : PureNash prisonersDilemma defect defect
isNashEquilibriumDD = pureNash (leftBestDefect defect) (rightBestDefect defect)

pdBestResponse : Action → Action
pdBestResponse _ = defect

pdBestResponseFixed : pdBestResponse defect ≡ defect
pdBestResponseFixed = refl

pdStep : Action × Action → Action × Action
pdStep _ = defect , defect

pdStep-stabilises : ∀ s → pdStep s ≡ (defect , defect)
pdStep-stabilises _ = refl

pdIter : Nat → Action × Action → Action × Action
pdIter zero s = s
pdIter (suc n) s = pdIter n (pdStep s)

pdIter-stabilises : ∀ n s → pdIter (suc n) s ≡ (defect , defect)
pdIter-stabilises zero s = refl
pdIter-stabilises (suc n) s = pdIter-stabilises n (defect , defect)

nashConvergenceWitness : NashCertificate
nashConvergenceWitness = nashCertificate defect defect isNashEquilibriumDD
