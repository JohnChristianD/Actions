{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusSignReLUComposition where

open import Agda.Builtin.Equality using (_≡_; refl; trans; cong)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_<_; _≤_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  ; zero8
  )
open import Data.Fin using (toℕ)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; gruState
  ; hidden
  ; matrices
  ; noise
  ; global
  ; gruStep
  ; GRUMatrices
  ; GRUNoise
  ; GlobalControl
  ; signReLU8
  ; FiniteUnary
  ; apply
  )
open import Exotic.ERL.FullCoupled.GRUCompositionAlgebra using
  ( stepAction
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( Fixed
  ; LyapunovCertificate
  ; iterate
  ; noNontrivialFiniteCycle
  ; OrbitNonFixed
  )
open import Exotic.ERL.FullCoupled.WatkinsDPG using
  ( WatkinsExploration
  ; sampledAction
  ; watkinsCut
  ; watkinsCut-preserves-action
  )

------------------------------------------------------------------------
-- The activation actually used by the finite GRU candidate path.
-- It is the piecewise finite truncation n ∸ 128.  This is the activation
-- entering gruCandidate; sparsemax is upstream and is not part of this
-- deterministic cycle transition.
------------------------------------------------------------------------

signReLU8-code :
  ∀ (x : Int8) →
  apply signReLU8 x ≡ int8OfNat (toℕ (code x) ∸ 128)
signReLU8-code x = refl

------------------------------------------------------------------------
-- Exact deterministic candidate-stage composition.
------------------------------------------------------------------------

candidateTransition : Int8 → Int8 → Int8
candidateTransition c h =
  apply signReLU8 (c + h)

------------------------------------------------------------------------
-- Generic finite window composition.  No probability or critic enters.
------------------------------------------------------------------------

record MonotoneLyapunovWindow : Set₁ where
  constructor monotoneLyapunovWindow
  field
    window : Int8 → Int8
    energy : Int8 → Nat
    nonIncrease : ∀ x → energy (window x) ≤ energy x
    strictMove : ∀ x → window x ≢ x → energy (window x) < energy x

open MonotoneLyapunovWindow public

record ComposedWindow (A B : MonotoneLyapunovWindow) : Set₁ where
  constructor composedWindow
  field
    commonEnergy : Int8 → Nat
    sameEnergy : commonEnergy ≡ energy A
    sameEnergyB : commonEnergy ≡ energy B
    crossNonIncrease :
      ∀ x → energy B (window A x) ≤ energy A x
    crossStrictMove :
      ∀ x →
      window B (window A x) ≢ x →
      energy B (window A x) < energy A x

open ComposedWindow public

------------------------------------------------------------------------
-- Composition interpolation theorem: if a deterministic finite window is
-- Lyapunov-nonincreasing and every moving composed step has one strict drop,
-- then the composition itself excludes every nontrivial finite n-cycle.
------------------------------------------------------------------------

composedWindowNoNontrivialFiniteCycle :
  ∀ {A B : MonotoneLyapunovWindow}
  (C : ComposedWindow A B) {s : Int8} (n : Nat) →
  let F = λ x → window B (window A x)
  in iterate F (suc n) s ≡ s →
     OrbitNonFixed F s →
     ⊥
composedWindowNoNontrivialFiniteCycle C =
  λ n cyc nf →
    let F = λ x → window B (window A x)
        L : LyapunovCertificate Int8 F
        L = record
          { energy = energy B
          ; strictDecrease = λ x not-fixed →
              crossStrictMove C x not-fixed
          }
    in noNontrivialFiniteCycle L n cyc nf

------------------------------------------------------------------------
-- Lift the actual signReLU candidate carrier into the full GRU state.
-- The non-hidden carrier is persisted by gruStep and therefore a hidden
-- Lyapunov law is enough to lift to the full-state deterministic transition.
------------------------------------------------------------------------

record SignReLUGRUDescent (x : Int8) : Set₁ where
  constructor signReLUGRUDescent
  field
    hiddenEnergy : Int8 → Nat
    hiddenStrictDecrease :
      ∀ (s : GRUState) →
      hidden (gruState
        (apply signReLU8 (hidden (gruStep s x)))
        (matrices s) (noise s) (global s)) ≢ hidden s →
      hiddenEnergy
        (hidden (gruState
          (apply signReLU8 (hidden (gruStep s x)))
          (matrices s) (noise s) (global s)))
      < hiddenEnergy (hidden s)

open SignReLUGRUDescent public

signReLUStep : Int8 → GRUState → GRUState
signReLUStep x s =
  let r = gruStep s x
  in gruState
      (apply signReLU8 (hidden r))
      (matrices r)
      (noise r)
      (global r)

signReLUStep-hidden :
  ∀ (x : Int8) (s : GRUState) →
  hidden (signReLUStep x s) ≡ apply signReLU8 (hidden (gruStep s x))
signReLUStep-hidden x s = refl

signReLU-Lyapunov :
  ∀ {x : Int8} →
  SignReLUGRUDescent x →
  LyapunovCertificate GRUState (signReLUStep x)
signReLU-Lyapunov D = record
  { energy = λ s → hiddenEnergy D (hidden s)
  ; strictDecrease = λ s not-fixed →
      hiddenStrictDecrease D s (λ q →
        not-fixed (cong (λ h → gruState h (matrices s) (noise s) (global s)) q))
  }

signReLU-GRU-noNontrivialFiniteCycle :
  ∀ {x : Int8}
  (D : SignReLUGRUDescent x)
  {s : GRUState} (n : Nat) →
  iterate (signReLUStep x) (suc n) s ≡ s →
  OrbitNonFixed (signReLUStep x) s →
  ⊥
signReLU-GRU-noNontrivialFiniteCycle D =
  noNontrivialFiniteCycle (signReLU-Lyapunov D)

------------------------------------------------------------------------
-- Watkins remains ceteris-paribus: it preserves the sampled action carrier,
-- while the deterministic cycle theorem concerns signReLU-GRU state flow.
------------------------------------------------------------------------

watkins-signReLU-ceteris-paribus :
  ∀ (e : WatkinsExploration) →
  sampledAction (watkinsCut e) ≡ sampledAction e
watkins-signReLU-ceteris-paribus = watkinsCut-preserves-action
