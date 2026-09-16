{-# OPTIONS --safe #-}

module Exotic.econlib.MatchingPennies where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)

data Action : Set where
  heads : Action
  tails : Action

record Game2 : Set₁ where
  constructor game2
  field
    payoff : Action → Action → Fin 256 × Fin 256

open Game2 public

matchingPennies : Game2
matchingPennies = game2 λ where
  heads heads → (fromℕ< (m%n<n 1 256) , fromℕ< (m%n<n 0 256))
  heads tails → (fromℕ< (m%n<n 0 256) , fromℕ< (m%n<n 1 256))
  tails heads → (fromℕ< (m%n<n 0 256) , fromℕ< (m%n<n 1 256))
  tails tails → (fromℕ< (m%n<n 1 256) , fromℕ< (m%n<n 0 256))

leftScore : Action → Action → Nat
leftScore a b with payoff matchingPennies a b
... | x , y = toℕ x

rightScore : Action → Action → Nat
rightScore a b with payoff matchingPennies a b
... | x , y = toℕ y

record PureNash (a b : Action) : Set where
  constructor pureNash
  field
    leftBest : ∀ a' → leftScore a' b ≤ leftScore a b
    rightBest : ∀ b' → rightScore a b' ≤ rightScore a b

natSelfLe : ∀ n → n ≤ n
natSelfLe zero = z≤n
natSelfLe (suc n) = s≤s (natSelfLe n)

oneNotLeZero : 1 ≤ 0 → heads ≢ heads
oneNotLeZero ()

matchingPennies-no-pure : ∀ {a b} → PureNash a b → a ≢ a
matchingPennies-no-pure {heads} {heads} h = oneNotLeZero (PureNash.leftBest h tails)
matchingPennies-no-pure {heads} {tails} h = oneNotLeZero (PureNash.rightBest h heads)
matchingPennies-no-pure {tails} {heads} h = oneNotLeZero (PureNash.rightBest h tails)
matchingPennies-no-pure {tails} {tails} h = oneNotLeZero (PureNash.leftBest h heads)

matchingPennies-bestReply-left : ∀ b →
  leftScore heads b ≡ suc zero
matchingPennies-bestReply-left heads = refl
matchingPennies-bestReply-left tails = refl

matchingPennies-bestReply-right : ∀ a →
  rightScore a tails ≡ suc zero
matchingPennies-bestReply-right heads = refl
matchingPennies-bestReply-right tails = refl

matchingPennies-no-stable-pure-profile : ∀ {a b} → PureNash a b → a ≢ a
matchingPennies-no-stable-pure-profile = matchingPennies-no-pure
