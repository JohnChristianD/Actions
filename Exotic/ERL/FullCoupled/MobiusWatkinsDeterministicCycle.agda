{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusWatkinsDeterministicCycle where

open import Agda.Builtin.Equality using (_≡_; refl; subst)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_<_) 
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; GRUMatrices
  ; GRUNoise
  ; GlobalControl
  ; gruState
  ; hidden
  ; matrices
  ; noise
  ; global
  ; gruStep
  )
open import Exotic.ERL.FullCoupled.GRUCompositionAlgebra using
  ( stepAction
  )
open import Exotic.ERL.FullCoupled.MobiusGRU using
  ( Mobius
  ; run
  ; identityMobius
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( LyapunovCertificate
  ; energy
  ; strictDecrease
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
-- The deterministic transition under discussion is the GRU recurrence
-- followed by a finite Mobius endomorphism of the newly produced hidden
-- coordinate. The parameter/noise/global carrier is otherwise unchanged.
------------------------------------------------------------------------

mobiusActivatedStep :
  Mobius → GRUState → Int8 → GRUState
mobiusActivatedStep a s x =
  let r = gruStep s x
  in gruState
       (run a (hidden r))
       (matrices r)
       (noise r)
       (global r)

mobiusActivatedHidden :
  Mobius → GRUState → Int8 → Int8
mobiusActivatedHidden a s x =
  run a (hidden (gruStep s x))

mobiusActivatedStep-hidden :
  ∀ (a : Mobius) (s : GRUState) (x : Int8) →
  hidden (mobiusActivatedStep a s x)
  ≡ mobiusActivatedHidden a s x
mobiusActivatedStep-hidden a s x = refl

------------------------------------------------------------------------
-- Identity activation recovers the original deterministic GRU action.
-- Thus the theorem below explicitly separates the bare GRU from its Mobius
-- modification instead of treating activation as an unnamed side condition.
------------------------------------------------------------------------

mobiusActivatedStep-identity :
  ∀ (s : GRUState) (x : Int8) →
  mobiusActivatedStep identityMobius s x ≡ stepAction x s
mobiusActivatedStep-identity s x = refl

------------------------------------------------------------------------
-- Exact lift from a strict hidden-coordinate descent law to a full-state
-- Lyapunov certificate. This is the composition point at which the
-- no-nontrivial-cycle theorem attaches.
------------------------------------------------------------------------

record MobiusHiddenDescent
  (a : Mobius)
  (x : Int8) : Set₁ where
  constructor mobiusHiddenDescent
  field
    hiddenEnergy : Int8 → Nat
    hiddenStrictDecrease :
      ∀ (s : GRUState) →
      mobiusActivatedHidden a s x ≢ hidden s →
      hiddenEnergy (mobiusActivatedHidden a s x) < hiddenEnergy (hidden s)

open MobiusHiddenDescent public

activatedStep-fixed-from-hidden :
  ∀ (a : Mobius) (x : Int8)
  (h : Int8) (m : GRUMatrices) (n : GRUNoise) (g : GlobalControl) →
  run a (hidden (gruStep (gruState h m n g) x)) ≡ h →
  mobiusActivatedStep a (gruState h m n g) x ≡ gruState h m n g
activatedStep-fixed-from-hidden a x h m n g q =
  subst
    (λ z → gruState z m n g)
    q
    refl

mobiusActivatedLyapunov :
  ∀ {a : Mobius} {x : Int8} →
  MobiusHiddenDescent a x →
  LyapunovCertificate GRUState (λ s → mobiusActivatedStep a s x)
mobiusActivatedLyapunov {a} {x} D =
  record
    { energy = λ s → hiddenEnergy D (hidden s)
    ; strictDecrease = λ s not-fixed →
        let
          hidden-not-fixed :
            mobiusActivatedHidden a s x ≢ hidden s
          hidden-not-fixed q =
            not-fixed
              (activatedStep-fixed-from-hidden
                 a x (hidden s) (matrices s) (noise s) (global s) q)
        in hiddenStrictDecrease D s hidden-not-fixed
    }

------------------------------------------------------------------------
-- The composed deterministic theorem: a Mobius-activated GRU has no
-- nontrivial finite n-cycle once the composed hidden transition satisfies
-- the strict finite Lyapunov descent law above.
------------------------------------------------------------------------

mobiusActivatedNoNontrivialFiniteCycle :
  ∀ {a : Mobius} {x : Int8}
  (D : MobiusHiddenDescent a x)
  {s : GRUState} (n : Nat) →
  iterate (mobiusActivatedStep a · x) (suc n) s ≡ s →
  OrbitNonFixed (mobiusActivatedStep a · x) s →
  ⊥
mobiusActivatedNoNontrivialFiniteCycle {a} {x} D =
  noNontrivialFiniteCycle (mobiusActivatedLyapunov {a = a} {x = x} D)

------------------------------------------------------------------------
-- Watkins ceteris-paribus: the cut changes trace classification but preserves
-- the sampled action carrier. The deterministic Mobius-GRU transition above
-- does not depend on the trace decision, so Watkins is not the source of the
-- finite-cycle exclusion.
------------------------------------------------------------------------

watkinsCeterisParibusAction :
  ∀ (e : WatkinsExploration) →
  sampledAction (watkinsCut e) ≡ sampledAction e
watkinsCeterisParibusAction = watkinsCut-preserves-action

------------------------------------------------------------------------
-- Bare-GRU specialization. With identity Mobius activation, the composed
-- theorem specializes exactly to the existing deterministic GRU action.
------------------------------------------------------------------------

bareGRUNoNontrivialFiniteCycle :
  ∀ {x : Int8}
  (D : MobiusHiddenDescent identityMobius x)
  {s : GRUState} (n : Nat) →
  iterate (stepAction x) (suc n) s ≡ s →
  OrbitNonFixed (stepAction x) s →
  ⊥
bareGRUNoNontrivialFiniteCycle D =
  mobiusActivatedNoNontrivialFiniteCycle D
