{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SparsemaxCriticWatkins where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.Int8SparsemaxTsallis2 using
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

-- The critic is the sole learned policy source.  There is no separate
-- deterministic actor parameterization: sparsemax is applied directly to Q.
record CriticState : Set where
  constructor criticState
  field
    qLeft qRight : Int8
open CriticState public

criticScores : CriticState → ActionScore
criticScores c = actionScore (qLeft c) (qRight c)

criticSparsemaxPolicy : CriticState → Sparsemax2Pair
criticSparsemaxPolicy c = sparsemax2Weights (criticScores c)

-- A finite signed dyadic q-log bonus is represented as an endogenous critic
-- transformation.  The actual generalized-log law is supplied separately.
record SignedQLogControl : Set where
  constructor signedQLogControl
  field
    enabled : BoolLike
    coefficient : Int8

data BoolLike : Set where
  enabled disabled : BoolLike

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

-- Algebraic equivalence theorem: a separate actor proxy is redundant whenever
-- its policy is definitionally/functionally constrained to criticSparsemaxPolicy.
record ActorProjectionEquivalence : Set₁ where
  constructor actorProjectionEquivalence
  field
    actorPolicy : CriticState → Sparsemax2Pair
    actorEqualsCritic : ∀ c → actorPolicy c ≡ criticSparsemaxPolicy c

actorProxyIsRedundant :
  ∀ E →
  ∀ c → ActorProjectionEquivalence.actorPolicy E c ≡ criticSparsemaxPolicy c
actorProxyIsRedundant E c = ActorProjectionEquivalence.actorEqualsCritic E c

-- A genuinely independent learned actor is not algebraically equivalent to this
-- critic-only construction; equivalence then requires an additional coupling law.
independentActorNotDefinitionallyEquivalent : Set
independentActorNotDefinitionallyEquivalent =
  ∀ {S : Set} (a q : S → Sparsemax2Pair) →
  (∀ s → a s ≡ q s) → ⊥
