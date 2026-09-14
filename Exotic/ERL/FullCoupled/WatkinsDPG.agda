{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.WatkinsDPG where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGActor
  ; DPGCritic
  ; actorForward
  ; criticForward
  )

------------------------------------------------------------------------
-- Watkins-style trace carrier.
-- keepTrace is the greedy continuation case; cutTrace is the Watkins
-- nongreedy-action trace cut.  The DPG actor remains unchanged.
------------------------------------------------------------------------

data TraceDecision : Set where
  keepTrace : TraceDecision
  cutTrace : TraceDecision

traceStep : TraceDecision → ℕ → ℕ
traceStep keepTrace n = suc n
traceStep cutTrace n = suc zero

watkinsTraceLength : List TraceDecision → ℕ
watkinsTraceLength [] = zero
watkinsTraceLength (keepTrace ∷ xs) = suc (watkinsTraceLength xs)
watkinsTraceLength (cutTrace ∷ xs) = suc zero

watkinsTraceLength-cut-head :
  ∀ (xs : List TraceDecision) →
  watkinsTraceLength (cutTrace ∷ xs) ≡ suc zero
watkinsTraceLength-cut-head xs = refl

watkinsTraceLength-empty :
  watkinsTraceLength [] ≡ zero
watkinsTraceLength-empty = refl

watkinsTraceLength-keep :
  ∀ (xs : List TraceDecision) →
  watkinsTraceLength (keepTrace ∷ xs) ≡ suc (watkinsTraceLength xs)
watkinsTraceLength-keep xs = refl

------------------------------------------------------------------------
-- Noisy-Net exploration may classify the sampled action as nongreedy
-- without mutating the actor/critic carrier.
------------------------------------------------------------------------

record WatkinsExploration : Set where
  constructor watkinsExploration
  field
    decision : TraceDecision
    sampledAction : Int8

open WatkinsExploration public

watkinsCut : WatkinsExploration → WatkinsExploration
watkinsCut e = watkinsExploration cutTrace (sampledAction e)

watkinsCut-preserves-action :
  ∀ (e : WatkinsExploration) →
  sampledAction (watkinsCut e) ≡ sampledAction e
watkinsCut-preserves-action e = refl

------------------------------------------------------------------------
-- Ceteris-paribus DPG actor/critic boundary.
------------------------------------------------------------------------

typeActor : DPGActor → Int8 → Int8
typeActor = actorForward

typeCritic : DPGCritic → Int8 → Int8
typeCritic = criticForward

watkinsActorPreserved :
  ∀ (a : DPGActor) (x : Int8) →
  typeActor a x ≡ actorForward a x
watkinsActorPreserved a x = refl

watkinsCriticPreserved :
  ∀ (c : DPGCritic) (x : Int8) →
  typeCritic c x ≡ criticForward c x
watkinsCriticPreserved c x = refl

------------------------------------------------------------------------
-- TD(0) degeneration is caused by trace truncation, not by the number of
-- recurrent matrices.  Once the head transition is cut, the active suffix
-- length is exactly one, so no earlier TD errors can be carried.
------------------------------------------------------------------------

allCuts : ℕ → List TraceDecision
allCuts zero = []
allCuts (suc n) = cutTrace ∷ allCuts n

allCuts-length-suc :
  ∀ (n : ℕ) →
  watkinsTraceLength (allCuts (suc n)) ≡ suc zero
allCuts-length-suc n = refl

watkins-one-step-under-cut :
  watkinsTraceLength (cutTrace ∷ []) ≡ suc zero
watkins-one-step-under-cut = refl

------------------------------------------------------------------------
-- Compact Watkins/DPG critic boundary.  This is actor-conditioned critic
-- evaluation; it intentionally does not assert that the actor is greedy.
------------------------------------------------------------------------

dpgWatkinsCriticStep :
  DPGCritic → DPGActor → Int8 → Int8
dpgWatkinsCriticStep c a x =
  criticForward c (actorForward a x)

dpgWatkinsCriticStep-law :
  ∀ (c : DPGCritic) (a : DPGActor) (x : Int8) →
  dpgWatkinsCriticStep c a x ≡
  criticForward c (actorForward a x)
dpgWatkinsCriticStep-law c a x = refl

------------------------------------------------------------------------
-- Regime classification makes the counterfactual explicit.
------------------------------------------------------------------------

data TraceRegime : Set where
  multiStep : TraceRegime
  oneStep : TraceRegime

watkinsRegime : List TraceDecision → TraceRegime
watkinsRegime [] = oneStep
watkinsRegime (cutTrace ∷ xs) = oneStep
watkinsRegime (keepTrace ∷ xs) = multiStep

cut-regime-is-one-step :
  ∀ (xs : List TraceDecision) →
  watkinsRegime (cutTrace ∷ xs) ≡ oneStep
cut-regime-is-one-step xs = refl
