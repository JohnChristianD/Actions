{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.WatkinsDPG where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Bool using (Bool; true; false)
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
-- Watkins-style trace carrier, kept algebraically separate from the
-- DPG actor.  A greedy continuation keeps the trace; a nongreedy action
-- cuts it.  This is the ceteris-paribus surface: the actor implementation
-- itself is unchanged.
------------------------------------------------------------------------

TraceDecision : Set
actionTrace : TraceDecision

-- The two constructors are deliberately semantic rather than a computed
-- argmax.  The finite DPG actor remains Int8 -> Int8 and callers supply the
-- greedy/nongreedy fact at the boundary where the ordered action semantics
-- are available.
data TraceDecision : Set where
  keepTrace : TraceDecision
  cutTrace : TraceDecision

actionTrace = keepTrace

traceStep : TraceDecision → ℕ → ℕ
actionTrace = keepTrace
traceStep keepTrace n = suc n
traceStep cutTrace n = suc zero

-- Canonical recursive carrier for the active Watkins suffix length.
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
-- Noisy-Net exploration interface.
-- The exploration mechanism is allowed to classify the sampled action as
-- nongreedy without changing the actor or critic carrier.
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
-- DPG actor/critic are retained ceteris paribus.
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
-- The TD(0) degeneration is an algebraic trace statement, not an
-- architectural statement: once every continuation is cut, the active
-- suffix has length one.  Thus no earlier TD errors can be carried by the
-- Watkins trace.
------------------------------------------------------------------------

allCuts : ℕ → List TraceDecision
allCuts zero = []
allCuts (suc n) = cutTrace ∷ allCuts n

allCuts-length :
  ∀ n →
  n ≡ zero →
  watkinsTraceLength (allCuts (suc n)) ≡ suc zero
allCuts-length n p = refl

watkins-one-step-under-cut :
  ∀ (x : Int8) →
  watkinsTraceLength (cutTrace ∷ []) ≡ suc zero
watkins-one-step-under-cut x = refl

------------------------------------------------------------------------
-- A compact DPG-backed critic boundary.  This is intentionally the
-- one-step critic evaluation of the actor-selected action; it does not
-- claim optimality of the actor by construction.
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
-- Counterfactual distinction: a three-matrix recurrent architecture does
-- not force TD(0).  The only formal route to the one-step collapse here is
-- trace truncation/cutting (or choosing the one-step lambda boundary).
------------------------------------------------------------------------

data TraceRegime : Set where
  multiStep : TraceRegime
  oneStep : TraceRegime

watkinsRegime : List TraceDecision → TraceRegime
watkinsRegime [] = oneStep
watkinsRegime (cutTrace ∷ xs) = oneStep
watkinsRegime (keepTrace ∷ xs) =
  multiStep

cut-regime-is-one-step :
  ∀ xs → watkinsRegime (cutTrace ∷ xs) ≡ oneStep
cut-regime-is-one-step xs = refl
