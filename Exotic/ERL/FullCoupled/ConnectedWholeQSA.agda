{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ConnectedWholeQSA where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.ConnectedGRUSemidirectQSA using
  ( ConnectedQSAState
  ; ConnectedMonolithState
  ; connectedStep
  ; WholeCouplingEnergy
  ; WholeCouplingCertificate
  ; connectedWholeLyapunov
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( Fixed
  ; LyapunovCertificate
  ; iterate
  ; OrbitNonFixed
  )
open import Exotic.ERL.FullCoupled.DeterministicQSA using
  ( HasDecidableEquality
  ; UniqueFixedPoint
  ; uniqueFixedPoint
  ; DeterministicQSAStyleCertificate
  ; deterministicQSAStyleConvergence
  ; deterministicQSAStyleNoNontrivialCycle
  ; ConvergesTo
  )

------------------------------------------------------------------------
-- One certificate at the connected monolith boundary. No component-level
-- convergence certificate is accepted here.
------------------------------------------------------------------------

record ConnectedWholeQSACertificate
  {x : Int8}
  {qStep : ConnectedQSAState → ConnectedQSAState}
  (E : WholeCouplingEnergy)
  (C : WholeCouplingCertificate E x qStep) : Set₁ where
  constructor connectedWholeQSACertificate
  field
    decidableEquality : HasDecidableEquality ConnectedMonolithState
    target : ConnectedMonolithState
    targetFixed : Fixed (connectedStep x qStep) target
    uniqueFixed : ∀ {s} → Fixed (connectedStep x qStep) s → s ≡ target

open ConnectedWholeQSACertificate public

connectedQSAStyleCertificate :
  ∀ {x : Int8}
    {qStep : ConnectedQSAState → ConnectedQSAState}
    (E : WholeCouplingEnergy)
    (C : WholeCouplingCertificate E x qStep)
  (Q : ConnectedWholeQSACertificate E C) →
  DeterministicQSAStyleCertificate
    ConnectedMonolithState
    (connectedStep x qStep)
connectedQSAStyleCertificate E C Q =
  record
    { lyapunov = connectedWholeLyapunov E C
    ; decidableEquality = decidableEquality Q
    ; target = target Q
    ; terminal = uniqueFixedPoint
        (targetFixed Q)
        (uniqueFixed Q)
    }

------------------------------------------------------------------------
-- Full deterministic QSA-style convergence of the connected composition.
-- The existing finite QSA proof is reused unchanged after the whole-state
-- certificate has been established.
------------------------------------------------------------------------

connectedWholeQSAConvergence :
  ∀ {x : Int8}
    {qStep : ConnectedQSAState → ConnectedQSAState}
    (E : WholeCouplingEnergy)
    (C : WholeCouplingCertificate E x qStep)
    (Q : ConnectedWholeQSACertificate E C)
    (s : ConnectedMonolithState) →
  ConvergesTo
    (connectedStep x qStep)
    (target Q)
    s
connectedWholeQSAConvergence E C Q s =
  deterministicQSAStyleConvergence
    (connectedQSAStyleCertificate E C Q)
    s

------------------------------------------------------------------------
-- The same whole-state certificate excludes every nontrivial finite cycle.
------------------------------------------------------------------------

connectedWholeQSANoNontrivialCycle :
  ∀ {x : Int8}
    {qStep : ConnectedQSAState → ConnectedQSAState}
    (E : WholeCouplingEnergy)
    (C : WholeCouplingCertificate E x qStep)
    (Q : ConnectedWholeQSACertificate E C)
    {s : ConnectedMonolithState} (n : Nat) →
  iterate (connectedStep x qStep) (suc n) s ≡ s →
  OrbitNonFixed (connectedStep x qStep) s →
  ⊥
connectedWholeQSANoNontrivialCycle E C Q =
  deterministicQSAStyleNoNontrivialCycle
    (connectedQSAStyleCertificate E C Q)

------------------------------------------------------------------------
-- The only missing QSA-specific inputs are now explicit: a real connected
-- target, its fixed-point proof, uniqueness, and finite-state equality. None
-- are fabricated from a component theorem.
------------------------------------------------------------------------
