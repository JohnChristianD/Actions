{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.DMCPFinite where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin; fromℕ<; toℕ)
open import Data.Nat using (_+_)
open import Data.Nat.DivMod using (m%n<n)
open import Relation.Nullary using (yes; no)

Scale : Set
Scale = Fin 4

Coordinate : Set
Coordinate = Fin 4

data DMCPAction : Set where
  neutral : DMCPAction
  perturb : Coordinate → Scale → DMCPAction

stepScale : Scale → Scale
stepScale x = fromℕ< (m%n<n (toℕ x + 1) 4)

DMCPState : Set
DMCPState = Coordinate → Scale

zeroDMCP : DMCPState
zeroDMCP _ = F.zero

dmcpStep : DMCPAction → DMCPState → DMCPState
dmcpStep neutral s = s
dmcpStep (perturb c k) s = λ j → ifSame c j k s

ifSame : Coordinate → Coordinate → Scale → DMCPState → Scale
ifSame c j k s with F._≟_ c j
... | yes _ = stepScale k
... | no _ = s j

neutral-preserves : ∀ s → dmcpStep neutral s ≡ s
neutral-preserves s = refl

finite-dmcp-witness : DMCPState
finite-dmcp-witness = zeroDMCP

finite-dmcp-nonempty : DMCPState
finite-dmcp-nonempty = finite-dmcp-witness
