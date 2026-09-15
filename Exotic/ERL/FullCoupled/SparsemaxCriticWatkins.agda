{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SparsemaxCriticWatkins where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.Int8SparsemaxLiteral using
  ( ActionScore
  ; actionScore
  ; Sparsemax2Pair
  ; sparsemax2Weights
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( LyapunovCertificate
  ; iterate
  ; OrbitNonFixed
  ; noNontrivialFiniteCycle
  )

-- The critic is the sole learned policy source. No separate deterministic
-- actor parameterization is part of the policy definition.
record CriticState : Set where
  constructor criticState
  field
    qLeft qRight : Int8
open CriticState public

criticScores : CriticState → ActionScore
criticScores c = actionScore (qLeft c) (qRight c)

criticSparsemaxPolicy : CriticState → Sparsemax2Pair
criticSparsemaxPolicy c = sparsemax2Weights (criticScores c)

data BoolLike : Set where
enabled disabled : BoolLike

-- The current monolith keeps this as an explicit finite critic-side control.
record SignedQLogControl : Set where
  constructor signedQLogControl
  field
    mode : BoolLike
    coefficient : Int8

record CriticKernel : Set₁ where
  constructor criticKernel
  field
    updateCritic : CriticState → Int8 → CriticState

data WatkinsTrace : Set where
  cut continue : WatkinsTrace

record Watkins1Kernel : Set₁ where
  constructor watkins1Kernel
  field
    greedy : CriticState → Int8 → BoolLike
    updateTrace : WatkinsTrace → BoolLike → WatkinsTrace

record SparsemaxCriticWatkinsState : Set where
  constructor sparsemaxCriticWatkinsState
  field
    critic : CriticState
    learnerSignal traceSignal : Int8
    trace : WatkinsTrace
open SparsemaxCriticWatkinsState public

record SparsemaxCriticWatkinsKernel : Set₁ where
  constructor sparsemaxCriticWatkinsKernel
  field
    criticKernel : CriticKernel
    traceKernel : Watkins1Kernel

wholeStep : SparsemaxCriticWatkinsKernel → SparsemaxCriticWatkinsState → SparsemaxCriticWatkinsState
wholeStep K s =
  sparsemaxCriticWatkinsState
    (CriticKernel.updateCritic (SparsemaxCriticWatkinsKernel.criticKernel K)
      (critic s) (learnerSignal s))
    (learnerSignal s)
    (traceSignal s)
    (Watkins1Kernel.updateTrace (SparsemaxCriticWatkinsKernel.traceKernel K)
      (trace s)
      (Watkins1Kernel.greedy (SparsemaxCriticWatkinsKernel.traceKernel K)
        (critic s) (learnerSignal s)))

record WholeCriticWatkinsLyapunov (K : SparsemaxCriticWatkinsKernel) : Set₁ where
  constructor wholeCriticWatkinsLyapunov
  field
    energy : SparsemaxCriticWatkinsState → Nat
    strictDecrease :
      ∀ s → wholeStep K s ≢ s → energy (wholeStep K s) < energy s

wholeCriticWatkinsCertificate :
  ∀ {K : SparsemaxCriticWatkinsKernel}
  → WholeCriticWatkinsLyapunov K
  → LyapunovCertificate SparsemaxCriticWatkinsState (wholeStep K)
wholeCriticWatkinsCertificate L =
  record
    { energy = WholeCriticWatkinsLyapunov.energy L
    ; strictDecrease = WholeCriticWatkinsLyapunov.strictDecrease L
    }

wholeCriticWatkinsNoNontrivialFiniteCycle :
  ∀ {K : SparsemaxCriticWatkinsKernel}
  (L : WholeCriticWatkinsLyapunov K)
  {s : SparsemaxCriticWatkinsState} (n : Nat)
  → iterate (wholeStep K) (suc n) s ≡ s
  → OrbitNonFixed {step = wholeStep K} s
  → ⊥
wholeCriticWatkinsNoNontrivialFiniteCycle L =
  noNontrivialFiniteCycle (wholeCriticWatkinsCertificate L)
