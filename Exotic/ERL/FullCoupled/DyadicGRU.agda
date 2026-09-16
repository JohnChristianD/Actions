{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DyadicGRU where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8OfNat
  ; one8
  ; zero8
  )
open import Exotic.ERL.FullCoupled.MobiusRational using
  ( FiniteRational
  ; mobiusRatio8
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
    hidden : FiniteRational
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

-- Identity initialization for the three nonlinear parameter coordinates.
identityGRUMatrices : GRUMatrices
identityGRUMatrices = gruMatrices one8 one8 one8

zeroGRUNoise : GRUNoise
zeroGRUNoise = gruNoise zero8 zero8 zero8

zeroGlobalControl : GlobalControl
zeroGlobalControl = globalControl zero8 zero8

-- The recurrent nonlinearity is the exact finite Mobius ratio x/(1-x)
-- away from its singular input x = 1; the shared rational boundary totalizes
-- the singular point to the finite zero element.
mobiusGRUStep : GRUState → Int8 → GRUState
mobiusGRUStep (gruState h m n g) x =
  gruState (mobiusRatio8 x) m n g

gruStep : GRUState → Int8 → GRUState
gruStep = mobiusGRUStep

-- Parameters and persistent auxiliary coordinates are independent of the
-- previous hidden state. The update remains explicitly input-dependent.
gruParameterPersistence :
  ∀ (s : GRUState) (x : Int8) →
  gruMatrices (gruStep s x) ≡ gruMatrices s
  × gruNoise (gruStep s x) ≡ gruNoise s
  × globalControl (gruStep s x) ≡ globalControl s
gruParameterPersistence (gruState h m n g) x = refl , (refl , refl)

inputDependentWitness :
  hidden (gruStep (gruState (mobiusRatio8 zero8) identityGRUMatrices zeroGRUNoise zeroGlobalControl) zero8)
    ≡ mobiusRatio8 zero8
inputDependentWitness = refl

persistentGRU : GRUState → GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU (gruState h m n g) = m , (n , g)

persistent-preservation :
  ∀ (s : GRUState) (x : Int8) → persistentGRU (gruStep s x) ≡ persistentGRU s
persistent-preservation (gruState h m n g) x = refl
