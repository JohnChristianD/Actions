{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.MR15Reachability where

open import Agda.Builtin.Equality using (_≡_; refl; subst; cong)
open import Data.Empty using (⊥)
open import Data.Fin as F using (Fin)
open import Exotic.ERL.Exploration.DyadicMR15GA using
  ( Dyadic
  ; MR15Index
  ; Population
  ; Mutation
  ; emptyPopulation
  ; mutate
  ; mutatePoint
  )
open import Exotic.ERL.Exploration.TheoremObligations using
  ( Reach
  ; mr15Step
  ; MR15AperiodicityObligation
  )

Uniform : Population → Set
Uniform p = ∀ i → p i ≡ p F.zero

empty-uniform : Uniform emptyPopulation
empty-uniform _ = refl

mutate-preserves-uniform : ∀ (m : Mutation) (i : MR15Index) (p : Population) →
  Uniform p → Uniform (mutate m i p)
mutate-preserves-uniform neutral i p u = u
mutate-preserves-uniform increment i p u with F._≟_ i F.zero
... | yes _ = λ j → cong (mutatePoint increment) (u j)
... | no _ = u
mutate-preserves-uniform decrement i p u with F._≟_ i F.zero
... | yes _ = λ j → cong (mutatePoint decrement) (u j)
... | no _ = u

step-preserves-uniform : ∀ {p q : Population} →
  mr15Step p q → Uniform p → Uniform q
step-preserves-uniform (m , (i , equality)) u =
  subst Uniform equality (mutate-preserves-uniform m i _ u)

reachable-uniform-from : ∀ {x y : Population} →
  Reach mr15Step x y → Uniform x → Uniform y
reachable-uniform-from here u = u
reachable-uniform-from (there step rest) u =
  reachable-uniform-from rest (step-preserves-uniform step u)

reachable-uniform : ∀ {p : Population} →
  Reach mr15Step emptyPopulation p → Uniform p
reachable-uniform here = empty-uniform
reachable-uniform (there step rest) =
  reachable-uniform-from rest (step-preserves-uniform step empty-uniform)

spike : Population
spike j with F._≟_ j F.zero
... | yes _ = F.suc F.zero
... | no _ = F.zero

zero-fin16≢one-fin16 : (F.zero : Fin 16) ≢ F.suc F.zero
zero-fin16≢one-fin16 ()

not-uniform-spike : ¬ Uniform spike
not-uniform-spike u = zero-fin16≢one-fin16 (u (F.suc F.zero))

currentMR15NotIrreducible : ¬ (∀ p q → Reach mr15Step p q)
currentMR15NotIrreducible allReach =
  not-uniform-spike (reachable-uniform (allReach emptyPopulation spike))

currentMR15AperiodicityImpossible : ¬ MR15AperiodicityObligation
currentMR15AperiodicityImpossible (_ , allReach) =
  currentMR15NotIrreducible allReach
