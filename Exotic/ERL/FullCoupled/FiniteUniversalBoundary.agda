{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteUniversalBoundary where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (pigeonhole; n<1+n; toℕ-injective; <-irrefl)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Function.Definitions using (Injective)
open import Data.Empty using (⊥)

iterate : ∀ {A : Set} → (A → A) → Nat → A → A
iterate f zero x = x
iterate f (suc n) x = iterate f n (f x)

orbit257 : ∀ (f : Fin 256 → Fin 256) (x : Fin 256) → Fin 257 → Fin 256
orbit257 f x i = iterate f (toℕ i) x

finiteOrbit-collision :
  ∀ (f : Fin 256 → Fin 256) (x : Fin 256) →
  ∃ λ i →
    ∃ λ j →
      i ≢ j ×
      iterate f (toℕ i) x ≡ iterate f (toℕ j) x
finiteOrbit-collision f x with
  pigeonhole (n<1+n 256) (orbit257 f x)
... | i , j , apart , eq = i , j , apart , eq

finiteCarrier-not-injective-on-unbounded-clock :
  ∀ (encode : Nat → Fin 256) →
  ¬ Injective _≡_ _≡_ encode
finiteCarrier-not-injective-on-unbounded-clock encode inj
  with pigeonhole (n<1+n 256) (λ i → encode (toℕ i))
... | i , j , apart , eq =
  <-irrefl (toℕ-injective (inj eq)) (toℕ-preserves-< apart)
  where
  toℕ-preserves-< : ∀ {i j : Fin 257} → i < j → toℕ i < toℕ j
  toℕ-preserves-< (s≤s p) = p


record TwoCounterConfig : Set where
  constructor twoCounterConfig
  field
    pc : Nat
    left right : Nat
open TwoCounterConfig public

record TwoCounterStep : Set where
  constructor twoCounterStep
  field
    runStep : TwoCounterConfig → TwoCounterConfig
open TwoCounterStep public

record TwoCounterSimulation
  (S : Set)
  (encode : TwoCounterConfig → S)
  (step : TwoCounterConfig → TwoCounterConfig) : Set where
  constructor twoCounterSimulation
  field
    runS : S → S
    stepLaw :
      ∀ c → runS (encode c) ≡ encode (step c)
open TwoCounterSimulation public

iterateMachine :
  ∀ {S : Set} (runS : S → S) → Nat → S → S
iterateMachine runS zero s = s
iterateMachine runS (suc n) s = iterateMachine runS n (runS s)

simulation-trace :
  ∀ {S : Set}
  {encode : TwoCounterConfig → S}
  {step : TwoCounterConfig → TwoCounterConfig}
  (sim : TwoCounterSimulation S encode step)
  n c →
  iterateMachine (runS sim) n (encode c) ≡
  encode (iterate step n c)
simulation-trace sim zero c = refl
simulation-trace sim (suc n) c =
  trans
    (cong (iterateMachine (runS sim) n) (stepLaw sim c))
    (simulation-trace sim n (step c))

finite-carrier-boundary :
  ∀ (encode : TwoCounterConfig → Fin 256) →
  ¬ Injective _≡_ _≡_ encode
finite-carrier-boundary encode =
  finiteCarrier-not-injective-on-unbounded-clock
    (λ x → x)
    (λ n → encode (twoCounterConfig n zero zero))

conditional-two-counter-transport :
  ∀ {S : Set}
  {encode : TwoCounterConfig → S}
  {step : TwoCounterConfig → TwoCounterConfig}
  (sim : TwoCounterSimulation S encode step) →
  ∀ n c →
  iterateMachine (runS sim) n (encode c) ≡
  encode (iterate step n c)
conditional-two-counter-transport sim n c =
  simulation-trace sim n c
