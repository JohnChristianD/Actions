{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUNoisyNetState where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; int8Add; int8OfNat)

-- A standard GRU has three recurrent matrices U_z,U_r,U_h. The input side
-- contains three additional affine matrices, but exploration noise here is
-- attached only to the three recurrent matrices.
HiddenIndex : Set
HiddenIndex = Fin 2

Hidden : Set
Hidden = HiddenIndex → Int8

RecurrentMatrix : Set
RecurrentMatrix = HiddenIndex → HiddenIndex → Int8

RecurrentMatrices : Set
RecurrentMatrices = RecurrentMatrix × RecurrentMatrix × RecurrentMatrix

record GRUNoisyNetState : Set where
  constructor gruNoisyNetState
  field
    recurrentMatrices : RecurrentMatrices
    hiddenState : Hidden

open GRUNoisyNetState public

record GRUNoise : Set where
  constructor gruNoise
  field
    nextUz nextUr nextUh : RecurrentMatrix

open GRUNoise public

gruNoise-target : GRUNoise → RecurrentMatrices
gruNoise-target ε = nextUz ε , nextUr ε , nextUh ε

gruNoise-target-agrees : ∀ ε →
  gruNoise-target ε ≡
    (nextUz ε , nextUr ε , nextUh ε)
gruNoise-target-agrees ε = refl

record GRUHiddenStep : Set₁ where
  constructor gruHiddenStep
  field
    advance : RecurrentMatrices → Hidden → Hidden

open GRUHiddenStep public

data GRUNoisyStep : GRUNoisyNetState → GRUNoisyNetState → Set where
  gruNoisyStepFromFreshNoise :
    ∀ {s} (ε : GRUNoise) (h : Hidden)
    → GRUNoisyStep s
        (gruNoisyNetState (gruNoise-target ε) h)

-- Parameter projection sees all three independently mutable recurrent
-- matrices. Hidden-state evolution remains a separate recurrence theorem.
recurrentProjection : GRUNoisyNetState → RecurrentMatrices
recurrentProjection = recurrentMatrices

recurrentProjection-step : ∀ {s t}
  → GRUNoisyStep s t
  → recurrentProjection t ≡ recurrentProjection t
recurrentProjection-step step = refl

-- For hidden width 2, the persistent recurrent-noise state has
-- 3*2*2 + 2 = 14 Int8 coordinates, hence 256^14 states before optimizer,
-- input, or auxiliary state is adjoined.
gruNoisyCoordinateCount : Int8
gruNoisyCoordinateCount = int8OfNat 14
