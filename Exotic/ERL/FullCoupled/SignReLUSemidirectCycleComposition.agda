{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SignReLUSemidirectCycleComposition where

open import Agda.Builtin.Equality using (_≡_; refl; trans; sym; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (_<_; _≤_)
open import Data.Nat.Properties using (<-trans)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; zero8
  )
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; GRUMatrices
  ; GRUNoise
  ; GlobalControl
  ; matrices
  ; noise
  ; global
  ; gruStep
  ; signReLU8
  ; apply
  )
open import Exotic.ERL.FullCoupled.GRUCompositionAlgebra using
  ( stepAction
  )
open import Exotic.ERL.FullCoupled.MobiusGroup using
  ( MobiusAction
  ; mobiusAction
  ; run
  ; identityAction
  ; composeAction
  ; composeAction-assoc
  )
open import Exotic.ERL.FullCoupled.FiniteSemidirectComposition using
  ( Semidirect
  ; semidirectMul
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( LyapunovCertificate
  ; iterate
  ; noNontrivialFiniteCycle
  ; OrbitNonFixed
  )

------------------------------------------------------------------------
-- signReLU is the recurrent candidate activation actually used by DyadicGRU.
-- It is represented here as a finite endomorphism. Associativity belongs to
-- composition of the resulting operators, not to a claim that this map is an
-- invertible Mobius-group element.
------------------------------------------------------------------------

signReLUWindow : MobiusAction
signReLUWindow = mobiusAction (apply signReLU8)

signReLUWindow-run :
  ∀ x →
  run signReLUWindow x ≡ apply signReLU8 x
signReLUWindow-run x = refl

signReLUWindow-zero :
  run signReLUWindow zero8 ≡ zero8
signReLUWindow-zero = refl

------------------------------------------------------------------------
-- Deep window composition. This is the operator-level content of recurrent
-- windowing: the same sequential operator can be regrouped associatively.
------------------------------------------------------------------------

deepWindow : Nat → MobiusAction → MobiusAction
deepWindow zero a = identityAction
deepWindow (suc n) a = composeAction (deepWindow n a) a

deepWindow-step :
  ∀ (n : Nat) (a : MobiusAction) (x : Int8) →
  run (deepWindow (suc n) a) x
  ≡ run (deepWindow n a) (run a x)
deepWindow-step n a x = refl

deepWindow-assoc-one-step :
  ∀ (a b c : MobiusAction) (x : Int8) →
  run (composeAction (composeAction a b) c) x
  ≡ run (composeAction a (composeAction b c)) x
deepWindow-assoc-one-step = composeAction-assoc

deepSignReLU : Nat → Int8 → Int8
deepSignReLU n x = run (deepWindow n signReLUWindow) x

deepSignReLU-zero :
  ∀ n → deepSignReLU n zero8 ≡ zero8
deepSignReLU-zero zero = refl
deepSignReLU-zero (suc n) =
  trans
    (deepWindow-step n signReLUWindow zero8)
    (deepSignReLU-zero n)

------------------------------------------------------------------------
-- Compositionally supplied Lyapunov law. Every primitive window shares one
-- energy, never increases it, and strictly decreases it on a moving state.
-- Then any two-window composition has the same strict descent law.
------------------------------------------------------------------------

record WindowDescent (W : Set) : Set₁ where
  constructor windowDescent
  field
    window : W → W
    energy : W → Nat
    nonIncrease : ∀ x → energy (window x) ≤ energy x
    strictMove : ∀ x → window x ≢ x → energy (window x) < energy x

open WindowDescent public

record ComposedWindowDescent (W : Set) : Set₁ where
  constructor composedWindowDescent
  field
    first : WindowDescent W
    second : WindowDescent W
    sameEnergy : energy first ≡ energy second

open ComposedWindowDescent public

composed-window-strict :
  ∀ {W : Set}
  (C : ComposedWindowDescent W)
  (x : W) →
  window second (window first x) ≢ x →
  energy second (window first x) < energy x
composed-window-strict C x moving =
  let
    drop₂ :
      energy (second C) (window (second C) (window (first C) x))
      < energy (second C) (window (first C) x)
    drop₂ =
      strictMove (second C) (window (first C) x) moving

    nonIncrease₁ :
      energy (first C) (window (first C) x)
      ≤ energy (first C) x
    nonIncrease₁ = nonIncrease (first C) x

    nonIncrease₂ :
      energy (second C) (window (first C) x)
      ≤ energy (second C) x
    nonIncrease₂ =
      subst
        (λ E → E (window (first C) x) ≤ E x)
        (sameEnergy C)
        nonIncrease₁
  in
    subst
      (λ E →
        E (window (second C) (window (first C) x)) < E x)
      (sameEnergy C)
      (<-trans drop₂ nonIncrease₂)

------------------------------------------------------------------------
-- Existing exact finite-cycle theorem discharges the composed window as soon
-- as its strict descent is constructed. No critic or stochastic assumption is
-- involved.
------------------------------------------------------------------------

composed-window-no-cycle :
  ∀ {W : Set}
  (C : ComposedWindowDescent W)
  (F : W → W)
  (F-law : ∀ x → F x ≡ window (second C) (window (first C) x)) →
  ∀ {x : W} (n : Nat) →
  iterate F (suc n) x ≡ x →
  OrbitNonFixed F x →
  ⊥
composed-window-no-cycle C F F-law n cyc nf =
  let
    L : LyapunovCertificate _ F
    L = record
      { energy = energy (second C)
      ; strictDecrease = λ x moving →
          let
            targetMoving :
              window (second C) (window (first C) x) ≢ x
            targetMoving q =
              moving (trans (F-law x) q)
          in
          subst
            (λ E → E (F x) < E x)
            (sym (F-law x))
            (composed-window-strict C x targetMoving)
      }
  in
    noNontrivialFiniteCycle L n cyc nf

------------------------------------------------------------------------
-- Semidirect transfer contract. A genuine GRU semidirect theorem needs an
-- explicit embedding of the concrete recurrent state into A × B. This record
-- makes that obligation executable instead of silently assuming the model is
-- a semidirect product.
------------------------------------------------------------------------

record SemidirectCycleEmbedding
  {A B : Set}
  (S : Semidirect A B)
  (X : Set) : Set₁ where
  constructor semidirectCycleEmbedding
  field
    encode : X → A × B
    decode : A × B → X
    decode-encode : ∀ x → decode (encode x) ≡ x
    carrierStep : A × B → A × B
    fixedElement : A × B
    carrierStep-law :
      ∀ p → carrierStep p ≡ semidirectMul S p fixedElement
    step : X → X
    step-law :
      ∀ x → decode (carrierStep (encode x)) ≡ step x

open SemidirectCycleEmbedding public

semidirect-embedded-no-cycle :
  ∀ {A B X : Set} {S : Semidirect A B}
  (E : SemidirectCycleEmbedding S X)
  (L : LyapunovCertificate X (step E))
  {x : X} (n : Nat) →
  iterate (step E) (suc n) x ≡ x →
  OrbitNonFixed (step E) x →
  ⊥
semidirect-embedded-no-cycle E L =
  noNontrivialFiniteCycle L

------------------------------------------------------------------------
-- Actual GRU persistent-state factorization. The recurrent step changes the
-- hidden coordinate while preserving matrices, exploration-noise coordinates,
-- and global optimizer/L2 control. This is the structural carrier needed by a
-- future concrete semidirect embedding.
------------------------------------------------------------------------

PersistentGRU : Set
PersistentGRU = GRUMatrices × (GRUNoise × GlobalControl)

persistentGRU : GRUState → PersistentGRU
persistentGRU s = matrices s , (noise s , global s)

gruStep-persistent :
  ∀ (s : GRUState) (x : Int8) →
  persistentGRU (gruStep s x) ≡ persistentGRU s
gruStep-persistent s x = refl

windowCarrier : Int8 → GRUState → GRUState
windowCarrier x = stepAction x

windowCarrier-persistent :
  ∀ (x : Int8) (s : GRUState) →
  persistentGRU (windowCarrier x s) ≡ persistentGRU s
windowCarrier-persistent x s = gruStep-persistent s x

------------------------------------------------------------------------
-- Final interpolation: associative signReLU windows give the operator
-- composition algebra; the componentwise descent theorem turns that algebra
-- into a strict Lyapunov law; the semidirect embedding transfers it to the
-- concrete GRU only when the remaining state-action factorization is supplied.
------------------------------------------------------------------------

signReLU-semidirect-interpolation :
  ∀ {A B X : Set} {S : Semidirect A B}
  (E : SemidirectCycleEmbedding S X)
  (L : LyapunovCertificate X (step E))
  {x : X} (n : Nat) →
  iterate (step E) (suc n) x ≡ x →
  OrbitNonFixed (step E) x →
  ⊥
signReLU-semidirect-interpolation E L =
  semidirect-embedded-no-cycle E L
