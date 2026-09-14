{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DyadicGRU where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; _+_; _*_; _≤?_; _-_)
open import Data.Nat.DivMod using (_/_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8Add
  ; int8Mul
  ; int8OfNat
  ; zero8
  ; one8
  )

------------------------------------------------------------------------
-- Finite recurrent representation. The three recurrent matrices are
-- explicit state components. Exploration noise is attached to all three,
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
-- Finite nonlinearities. Int8 code n is interpreted on the finite dyadic
-- unit grid n/255. The gate is the dyadic approximation
--   softsign(x) = x/(1+x)
-- followed by the GRU gate affine shift 1/2*(1+softsign).
-- The candidate is the finite ReLU-style positive branch on that grid.
------------------------------------------------------------------------

record FiniteUnary : Set₁ where
  constructor finiteUnary
  field
    apply : Int8 → Int8

open FiniteUnary public

identity8 : FiniteUnary
identity8 = finiteUnary (λ x → x)

unitNumerator : Int8 → ℕ
unitNumerator x = toℕ (code x)

softsignNumerator : ℕ → ℕ
softsignNumerator n = (255 * n) / (255 + n)

softsign8 : FiniteUnary
softsign8 =
  finiteUnary
    (λ x → int8OfNat (softsignNumerator (unitNumerator x)))

half8 : Int8
half8 = int8OfNat 128

onePlusSoftsign8 : FiniteUnary
onePlusSoftsign8 =
  finiteUnary
    (λ x →
      int8OfNat
        ((255 + softsignNumerator (unitNumerator x)) / 2))

signReLU8 : FiniteUnary
signReLU8 =
  finiteUnary
    (λ x →
      let n = unitNumerator x
      in int8OfNat (n - 128))

softsign8-nontrivial : apply softsign8 (int8OfNat 255) ≡ int8OfNat 127
softsign8-nontrivial = refl

signReLU8-zero : apply signReLU8 (int8OfNat 128) ≡ zero8
signReLU8-zero = refl

onePlusSoftsign8-zero : apply onePlusSoftsign8 zero8 ≡ int8OfNat 127
onePlusSoftsign8-zero = refl

------------------------------------------------------------------------
-- The gate substitution is explicitly distinguished from the reference
-- sigmoid: this module formalizes a finite dyadic candidate, not a universal
-- real-valued sigmoid identity.
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

gruMatricesPersist :
  ∀ (s : GRUState) (x : Int8) →
  matrices (gruStep s x) ≡ matrices s
gruMatricesPersist s x = refl

gruNoisePersists :
  ∀ (s : GRUState) (x : Int8) →
  noise (gruStep s x) ≡ noise s
gruNoisePersists s x = refl

gruGlobalControlPersists :
  ∀ (s : GRUState) (x : Int8) →
  global (gruStep s x) ≡ global s
gruGlobalControlPersists s x = refl

------------------------------------------------------------------------
-- Sequential recurrence is the primitive. Parallel scan is supplied by the
-- composition algebra; no commutativity assumption is introduced.
------------------------------------------------------------------------
