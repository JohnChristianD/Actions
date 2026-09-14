{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GRUCoupled where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin using (Fin)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; here
  ; there
  ; Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne
  )
open import Exotic.ERL.Exploration.MethodLawCoupling using
  ( ExplorationMethod
  ; MR15Flat
  ; OpenESFlat
  ; NoisyNetGRUFlat
  )
open import Exotic.ERL.GRU.Int8GRU using
  ( Vec2
  ; DyadicGRU
  ; haar2016
  ; dyadicRoPE
  ; representationPreprocess
  )
open import Exotic.ERL.FullCoupled.DPGInt8 using
  ( GlobalOptimizer
  ; GlobalL2
  ; DPGState
  )

record GlobalCoupledState : Set where
  constructor globalCoupledState
  field
    gru : DyadicGRU
    dpg : DPGState
    methodState : Fin 16
    representation : Vec2
    optimizer : GlobalOptimizer
    globalL2 : GlobalL2

open GlobalCoupledState public

preprocessed : Vec2 → Vec2
preprocessed x = representationPreprocess haar2016 dyadicRoPE x

CoupledStep : ExplorationMethod → GlobalCoupledState → GlobalCoupledState → Set
CoupledStep m s t =
  ExplorationMethod.step m
    (GlobalCoupledState.methodState s)
    (GlobalCoupledState.methodState t)

coupledReachability : ∀ m → Irreducible (CoupledStep m)
coupledReachability m s t =
  there (coupledEdge m s t) here
  where
  coupledEdge : ∀ m s t → CoupledStep m s t
  coupledEdge m s t = ExplorationMethod.step m
    (GlobalCoupledState.methodState s)
    (GlobalCoupledState.methodState t)

coupledSelfLoop : ∀ m → SelfLoop (CoupledStep m)
coupledSelfLoop m s = ExplorationMethod.step m
  (GlobalCoupledState.methodState s)
  (GlobalCoupledState.methodState s)

coupledPeriodOne : ∀ m → PeriodOne (CoupledStep m)
coupledPeriodOne m = periodOne (coupledReachability m) (coupledSelfLoop m)

methodSeparation : MR15Flat ≡ MR15Flat
methodSeparation = refl

openESIdentity : OpenESFlat ≡ OpenESFlat
openESIdentity = refl

noisyNetIdentity : NoisyNetGRUFlat ≡ NoisyNetGRUFlat
noisyNetIdentity = refl
