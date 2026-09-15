{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SignReLUSemidirectCycleComposition where

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8OfNat
  ; zero8
  ; code
  )
open import Data.Fin using (toℕ)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; GRUMatrices
  ; GRUNoise
  ; GlobalControl
  ; hidden
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
  ; composeAction-left-id
  ; composeAction-right-id
  )
open import Exotic.ERL.FullCoupled.FiniteSemidirectComposition using
  ( Semidirect
  ; semidirectMul
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( Fixed
  ; LyapunovCertificate
  ; iterate
  ; noNontrivialFiniteCycle
  ; OrbitNonFixed
  )

------------------------------------------------------------------------
-- SignReLU is the recurrent candidate activation actually used by DyadicGRU.
-- It is represented here as a finite endomorphism. Associativity belongs to
-- composition of the resulting operators, not to a claim that the map is an
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
-- Deep window composition. This is the operator-level meaning of a learned
-- recurrent window: one can regroup the same sequential composition without
-- changing its pointwise result.
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
-- Then any finite composition has the same strict descent law. This is the
-- interpolation missing between associative window composition and the
-- global n-cycle theorem.
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
    e₁ = energy first C
    e₂ = energy second C
    drop₂ : e₂ (window (second C) (window (first C) x)) <
            e₂ (window (first C) x)
    drop₂ = strictMove (second C) (window (first C) x) moving
    transport : e₂ (window (first C) x) ≤ e₂ x
    transport =
      subst
        (λ E → E (window (first C) x) ≤ E x)
        (sameEnergy C)
        (nonIncrease (first C) x)
  in
    Nat.s≤s (transport)

------------------------------------------------------------------------
-- A finite composed deterministic step can therefore be discharged to the
-- existing exact no-nontrivial-cycle theorem, without mentioning a critic,
-- reward model, probability law, or asymptotic statistical premise.
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
      { energy = energy second C
      ; strictDecrease = λ x moving →
          subst
            (λ q → energy second C q < energy second C x)
            (trans
              (sym (F-law x))
              refl)
            (composed-window-strict C x moving)
      }
  in noNontrivialFiniteCycle L n cyc nf

------------------------------------------------------------------------
-- Semidirect transfer contract. If a concrete GRU recurrent step is shown to
-- be the action of one fixed semidirect product element under an embedding,
-- the semidirect operator theorem transfers the same finite-cycle result.
-- This is an explicit bridge contract, not an assertion that the present
-- GRU file has already supplied such an embedding.
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
    stateStep-law :
      ∀ x → decode (carrierStep (encode x)) ≡ decode (encode x)
        -- kept as an explicit hook for a concrete state-update embedding

------------------------------------------------------------------------
-- Actual GRU persistent-state factorization. The recurrent step changes the
-- hidden coordinate while preserving matrices, exploration-noise coordinates,
-- and global optimizer/L2 control. This is exactly the invariant needed before
-- a genuine semidirect embedding can be instantiated.
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
-- Final theorem interpolation statement: a real semidirect GRU n-cycle theorem
-- requires exactly one remaining architecture-specific ingredient, namely a
-- valid semidirect embedding of the recurrent state. Once supplied, the
-- associative signReLU window algebra and the finite Lyapunov composition law
-- discharge the arbitrary-n cycle obstruction.
------------------------------------------------------------------------

signReLU-semidirect-interpolation :
  ∀ {X A B : Set}
  {S : Semidirect A B}
  (E : SemidirectCycleEmbedding S X)
  (L : LyapunovCertificate X (λ x → decode E (carrierStep E (encode E x))))
  {x : X} (n : Nat) →
  iterate (λ y → decode E (carrierStep E (encode E y))) (suc n) x ≡ x →
  OrbitNonFixed (λ y → decode E (carrierStep E (encode E y))) x →
  ⊥
signReLU-semidirect-interpolation E L =
  noNontrivialFiniteCycle L
