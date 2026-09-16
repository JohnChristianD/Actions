{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SparsemaxCriticWatkins where

open import Agda.Builtin.Equality using (_≡_; _≢_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int as I
open import Data.Empty using (⊥)
open import Data.Fin using (toℕ)
open import Data.Nat using (_∸_; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; code)
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( LyapunovCertificate
  ; iterate
  ; OrbitNonFixed
  ; noNontrivialFiniteCycle
  )

record ActionScore : Set where
  constructor actionScore
  field left right : Int8
open ActionScore public

Sparsemax2Pair : Set
Sparsemax2Pair = Int8 × Int8

signedCode : Int8 → I.Int
signedCode x with toℕ (code x) <ᵇ 128
... | true = I.pos (toℕ (code x))
... | false = I.negsuc (255 ∸ toℕ (code x))

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

halfInt : I.Int → I.Int
halfInt (I.pos n) = I.pos (halfNat n)
halfInt (I.negsuc n) = I.pos zero

clampQ7 : I.Int → Int8
clampQ7 (I.pos n) with n <ᵇ 129
... | true = int8OfNat n
... | false = int8OfNat 128
clampQ7 (I.negsuc n) = int8OfNat 0

complement128 : Int8 → Int8
complement128 x = int8OfNat (128 ∸ toℕ (code x))

sparsemax2Weights : ActionScore → Sparsemax2Pair
sparsemax2Weights (actionScore l r) =
  let d = I._-_ (signedCode l) (signedCode r)
      leftWeight = clampQ7 (halfInt (I._+_ (I.pos 128) (I._*_ (I.pos 8) d)))
  in leftWeight , complement128 leftWeight

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

-- Least semantic value of signed Q7 Int8 is -128, represented by code 128.
maxPessimisticCritic : CriticState
maxPessimisticCritic = criticState (int8OfNat 128) (int8OfNat 128)

maxPessimisticCritic-law :
  qLeft maxPessimisticCritic ≡ int8OfNat 128 ×
  qRight maxPessimisticCritic ≡ int8OfNat 128
maxPessimisticCritic-law = refl , refl

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
  → OrbitNonFixed s
  → ⊥
wholeCriticWatkinsNoNontrivialFiniteCycle L =
  noNontrivialFiniteCycle (wholeCriticWatkinsCertificate L)
