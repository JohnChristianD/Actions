{-# OPTIONS --safe #-}
module Exotic.econlib.dyadic.Econlib where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin)
open import Exotic.econlib.dyadic.Dyadic using
  ( Dyadic
  ; zeroᵈ
  ; _≤ᵈ_
  )

------------------------------------------------------------------------
-- Finite fragment selected from Econlib's Equilibrium, GameTheory, and
-- Optimization folders.  Continuous/real analysis is deliberately absent.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Optimization
------------------------------------------------------------------------

record DyadicObjective (n : Nat) : Set where
  constructor dyadicObjective
  field
    value : Fin n → Dyadic

open DyadicObjective public

record Maximizes {n : Nat} (f : DyadicObjective n) (x : Fin n) : Set where
  constructor maximizes
  field
    dominates : ∀ y → value f y ≤ᵈ value f x

optimal-self :
  ∀ {n} {f : DyadicObjective n} {x} → Maximizes f x → value f x ≤ᵈ value f x
optimal-self h = dominates h _

------------------------------------------------------------------------
-- Game theory
------------------------------------------------------------------------

record FiniteGame (players strategies : Nat) : Set where
  constructor finiteGame
  field
    payoff : Fin players → (Fin strategies → Fin strategies) → Dyadic
    deviate :
      (Fin strategies → Fin strategies) →
      Fin players → Fin strategies →
      Fin strategies → Fin strategies

open FiniteGame public

record BestResponse
  {players strategies : Nat}
  (g : FiniteGame players strategies)
  (p : Fin players)
  (profile : Fin strategies → Fin strategies)
  (choice : Fin strategies) : Set where
  constructor bestResponse
  field
    optimalAgainst :
      ∀ alternative →
      payoff g p (deviate g profile p alternative) ≤ᵈ
      payoff g p (deviate g profile p choice)

record NashEquilibrium
  {players strategies : Nat}
  (g : FiniteGame players strategies)
  (profile : Fin strategies → Fin strategies) : Set where
  constructor nashEquilibrium
  field
    eachPlayerBest : ∀ p → BestResponse g p profile (profile p)

nash-implies-best-response :
  ∀ {players strategies} {g : FiniteGame players strategies}
    {profile} → NashEquilibrium g profile →
    ∀ p → BestResponse g p profile (profile p)
nash-implies-best-response h = eachPlayerBest h

------------------------------------------------------------------------
-- Equilibrium / market clearing
------------------------------------------------------------------------

record Market (agents goods : Nat) : Set where
  constructor market
  field
    aggregateDemand : Fin goods → Dyadic
    supply : Fin goods → Dyadic

open Market public

record MarketEquilibrium
  {agents goods : Nat}
  (m : Market agents goods) : Set where
  constructor marketEquilibrium
  field
    clears : ∀ good → aggregateDemand m good ≡ supply m good

market-equilibrium-clears :
  ∀ {agents goods} {m : Market agents goods} →
  MarketEquilibrium m →
  ∀ good → aggregateDemand m good ≡ supply m good
market-equilibrium-clears h = clears h

------------------------------------------------------------------------
-- Pure dyadic welfare comparison.
------------------------------------------------------------------------

record WelfareWitness (n : Nat) : Set where
  constructor welfareWitness
  field
    chosen : Fin n
    welfare : Fin n → Dyadic
    optimal : ∀ y → welfare y ≤ᵈ welfare chosen
