{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DyadicGRU where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_∸_)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (toℕ)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8OfNat
  ; code
  )

record GRUMatrices : Set where
  constructor gruMatrices
  field
    matrixA matrixB matrixC : Int8
open GRUMatrices public

record GRUNoise : Set where
  constructor gruNoise
  field
    noiseA noiseB noiseC : Int8
open GRUNoise public

record GlobalControl : Set where
  constructor globalControl
  field
    optimizerToken l2Token : Int8
open GlobalControl public

record GRUState : Set where
  constructor gruState
  field
    hidden : Int8
    gruMatrices : GRUMatrices
    gruNoise : GRUNoise
    globalControl : GlobalControl
open GRUState public

matrices : GRUState → GRUMatrices
matrices = gruMatrices

noise : GRUState → GRUNoise
noise = gruNoise

global : GRUState → GlobalControl
global = globalControl

record FiniteUnary : Set₁ where
  constructor finiteUnary
  field
    apply : Int8 → Int8
open FiniteUnary public

unitNumerator : Int8 → Nat
unitNumerator x = toℕ (code x)

-- This is the finite Int8 sign/ReLU candidate used by the recurrence track.
signReLU8 : FiniteUnary
signReLU8 = finiteUnary
  (λ x → int8OfNat (unitNumerator x ∸ 128))

-- The recurrent update changes only hidden state. Matrices, noise, and global
-- control are persistent coordinates and therefore are preserved definitionally.
gruStep : GRUState → Int8 → GRUState
gruStep (gruState h m n g) x =
  gruState (apply signReLU8 (int8Add h x)) m n g

persistentGRU : GRUState → GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU (gruState h m n g) = m , (n , g)

persistent-preservation :
  ∀ (s : GRUState) (x : Int8) → persistentGRU (gruStep s x) ≡ persistentGRU s
persistent-preservation (gruState h m n g) x = refl
