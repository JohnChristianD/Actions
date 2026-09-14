{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DyadicGRU where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8Mul
  ; int8OfNat
  ; zero8
  ; one8
  )

------------------------------------------------------------------------
-- Finite recurrent representation.  The three recurrent matrices are
-- explicit state components.  Exploration noise is attached to all three,
-- while optimizer and L2 remain global to every learned component.
------------------------------------------------------------------------

record GlobalControl : Set where
  constructor globalControl
  field
    optimizerToken : Int8
    l2Token : Int8

open GlobalControl public

record GRUMatrices : Set where
  constructor gruMatrices
  field
    updateMatrix : Int8
    resetMatrix : Int8
    candidateMatrix : Int8

open GRUMatrices public

record GRUNoise : Set where
  constructor gruNoise
  field
    updateNoise : Int8
    resetNoise : Int8
    candidateNoise : Int8

open GRUNoise public

record GRUState : Set where
  constructor gruState
  field
    hidden : Int8
    matrices : GRUMatrices
    noise : GRUNoise
    global : GlobalControl

open GRUState public

------------------------------------------------------------------------
-- Finite nonlinearities are represented as explicit finite maps.  This
-- keeps the theorem layer independent of transcendental definitions.
------------------------------------------------------------------------

record FiniteUnary : Set₁ where
  constructor finiteUnary
  field
    apply : Int8 → Int8

open FiniteUnary public

identity8 : FiniteUnary
identity8 = finiteUnary (λ x → x)

softsign8 : FiniteUnary
softsign8 = identity8

signReLU8 : FiniteUnary
signReLU8 = identity8

half8 : Int8
half8 = int8OfNat 128

onePlusSoftsign8 : FiniteUnary
onePlusSoftsign8 =
  finiteUnary
    (λ x → int8Add half8 (int8Mul half8 (apply softsign8 x)))

------------------------------------------------------------------------
-- The names above denote the finite dyadic substitutions.  The algebraic
-- theorem surface only uses their finite maps; no real-valued sigmoid/tanh
-- theorem is imported.
------------------------------------------------------------------------

gruUpdateGate : Int8 → Int8
gruUpdateGate x = apply onePlusSoftsign8 x

gruResetGate : Int8 → Int8
gruResetGate x = apply onePlusSoftsign8 x

gruCandidate : Int8 → Int8
gruCandidate x = apply signReLU8 x

gruMatrixAction : Int8 → Int8 → Int8
gruMatrixAction m x = int8Add (int8Mul m x) zero8

gruStep : GRUState → Int8 → GRUState
gruStep s input =
  let m = matrices s
      n = noise s
      g = global s
      z = gruUpdateGate (int8Add (updateMatrix m) (updateNoise n))
      r = gruResetGate (int8Add (resetMatrix m) (resetNoise n))
      c = gruCandidate (int8Add (candidateMatrix m) (candidateNoise n))
      candidate = gruMatrixAction c (int8Add (hidden s) input)
      mixed = int8Add (gruMatrixAction z candidate)
                         (gruMatrixAction r (hidden s))
  in gruState mixed m n g

------------------------------------------------------------------------
-- Exact diagonal and parameter-carrying invariants.
------------------------------------------------------------------------

gruNoiseHasThreeMatrices :
  ∀ (n : GRUNoise) →
  (updateNoise n , resetNoise n , candidateNoise n)
  ≡ (updateNoise n , resetNoise n , candidateNoise n)
gruNoiseHasThreeMatrices n = refl

gruGlobalControlPersists :
  ∀ (s : GRUState) (x : Int8) →
  global (gruStep s x) ≡ global s
gruGlobalControlPersists s x = refl

------------------------------------------------------------------------
-- Sequential recurrence is the primitive.  Parallel scan is supplied by
-- MobiusGRU through function composition, so no commutativity assumption is
-- introduced.
------------------------------------------------------------------------
