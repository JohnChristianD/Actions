{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AllSafeCombined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.Exploration.DyadicLaws using
  ( Law
  ; Method
  ; flatDyadic
  ; noisyNetGRU
  ; law-has-zero
  ; law-has-unit-generator
  )
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; SelfLoop
  ; PeriodOne
  )
open import Exotic.ERL.FullCoupled.DyadicMethodLawCoupling using
  ( CanonicalState
  ; CoupledStep
  ; coupledIrreducible
  ; coupledSelfLoop
  ; coupledPeriodOne
  )
open import Exotic.ERL.FullCoupled.MobiusGRU using
  ( Mobius
  ; compose
  ; compose-assoc
  ; compose-identity-left
  ; compose-identity-right
  )
open import Exotic.ERL.FullCoupled.DyadicRepresentation using
  ( representationCompose
  )
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGActor
  ; DPGCritic
  ; actorAction
  ; ActorAction
  ; actorForward
  ; criticForward
  ; composeActorAction
  ; actorCompositionClosed
  ; actorCompositionAssociative
  ; actorComposition-left-identity
  ; actorComposition-right-identity
  ; SharedDPGBand
  ; sharedActor
  ; sharedCritic
  )
open import Exotic.ERL.FullCoupled.FiniteHaarSparsemaxRoPE using
  ( Int8Pair
  ; frontEnd
  ; frontEnd-expanded
  ; sparsemax2-hard-sparsity-left
  ; sparsemax2-hard-sparsity-right
  ; frontEndToGRU
  ; ropeQuarter
  ; haar2
  ; sparsemax2
  )
open import Exotic.ERL.FullCoupled.DPGBellmanHaarComposition using
  ( Q
  ; GreedyPolicy
  ; IsGreedy
  ; maxQ
  ; maxQBootstrap
  ; greedyPolicyBootstrap
  ; DPG-maxQ-bootstrap-equivalence
  ; haarInt8
  ; haar-columns-orthogonal
  ; haar-column-left-norm
  ; haar-column-right-norm
  ; commonPrefixThenHeads
  ; commonPrefix-factorization
  )
open import Exotic.ERL.FullCoupled.PromotionComposition using
  ( DiscretePQNVariant
  ; discretePQNTarget
  ; discretePQN-target-common
  ; promotedDPGActor
  ; promotedDPGActor-total
  ; promotedActorOptimizer
  ; promotedActorL2
  ; promotedCriticOptimizer
  ; promotedCriticL2
  ; promotedActor-under-perturbation
  ; promotedCritic-under-perturbation
  ; promotedActorCompose
  ; promotedCriticCompose
  ; promotedComposition-law
  ; promotedComposition-actor-optimizer
  ; promotedComposition-actor-L2
  ; promotedComposition-critic-optimizer
  ; promotedComposition-critic-L2
  ; promotedGreedyTarget
  )
open import Exotic.ERL.FullCoupled.WatkinsDPG using
  ( TraceDecision
  ; keepTrace
  ; cutTrace
  ; watkinsTraceLength
  ; watkinsTraceLength-cut-head
  ; watkinsTraceLength-empty
  ; watkinsTraceLength-keep
  ; WatkinsExploration
  ; sampledAction
  ; watkinsCut
  ; watkinsCut-preserves-action
  ; watkinsActorPreserved
  ; watkinsCriticPreserved
  ; allCuts
  ; allCuts-length-suc
  ; watkins-one-step-under-cut
  ; dpgWatkinsCriticStep
  ; dpgWatkinsCriticStep-law
  ; TraceRegime
  ; multiStep
  ; oneStep
  ; watkinsRegime
  ; cut-regime-is-one-step
  )

canonicalLaw0 : Law
canonicalLaw0 = flatDyadic

canonicalMethod0 : Method
canonicalMethod0 = noisyNetGRU

canonicalState : Set
canonicalState = CanonicalState

canonicalIrreducible :
  ∀ (m : Method) →
  ∀ s t → Reach (CoupledStep flatDyadic m) s t
canonicalIrreducible = coupledIrreducible

canonicalSelfLoop :
  ∀ (m : Method) →
  SelfLoop (CoupledStep flatDyadic m)
canonicalSelfLoop = coupledSelfLoop

canonicalPeriodOne :
  ∀ (m : Method) →
  PeriodOne (CoupledStep flatDyadic m)
canonicalPeriodOne = coupledPeriodOne

canonicalFlatZero = law-has-zero flatDyadic
canonicalFlatGenerator = law-has-unit-generator flatDyadic

canonicalRepresentationLaw :
  ∀ x → representationCompose x ≡ representationCompose x
canonicalRepresentationLaw x = refl

canonicalMobiusAssoc :
  ∀ (a b c : Mobius) →
  compose (compose a b) c ≡ compose a (compose b c)
canonicalMobiusAssoc = compose-assoc

canonicalMobiusLeft : ∀ a → compose (record { run = λ x → x }) a ≡ a
canonicalMobiusLeft a = compose-identity-left a

canonicalMobiusRight : ∀ a → compose a (record { run = λ x → x }) ≡ a
canonicalMobiusRight a = compose-identity-right a

canonicalFiniteIdentity :
  ∀ (x : Int8) → x ≡ x
canonicalFiniteIdentity x = refl

canonicalActorClosure :
  ∀ (a b : DPGActor) (x : Int8) →
  composeActorAction (actorAction a) (actorAction b) x ≡
  actorAction a (actorAction b x)
canonicalActorClosure = actorCompositionClosed

canonicalActorAssoc :
  ∀ (f g h : ActorAction) (x : Int8) →
  composeActorAction (composeActorAction f g) h x ≡
  composeActorAction f (composeActorAction g h) x
canonicalActorAssoc = actorCompositionAssociative

canonicalActorLeftId :
  ∀ (f : ActorAction) (x : Int8) →
  composeActorAction (λ y → y) f x ≡ f x
canonicalActorLeftId = actorComposition-left-identity

canonicalActorRightId :
  ∀ (f : ActorAction) (x : Int8) →
  composeActorAction f (λ y → y) x ≡ f x
canonicalActorRightId = actorComposition-right-identity

canonicalFrontEndLaw :
  ∀ (p : Int8Pair) →
  frontEnd p ≡ ropeQuarter (haar2 (sparsemax2 p))
canonicalFrontEndLaw = frontEnd-expanded

canonicalHardSparseLeft : sparsemax2-hard-sparsity-left
canonicalHardSparseLeft = sparsemax2-hard-sparsity-left

canonicalHardSparseRight : sparsemax2-hard-sparsity-right
canonicalHardSparseRight = sparsemax2-hard-sparsity-right

canonicalFrontEndToGRU :
  ∀ (p : Int8Pair) → frontEndToGRU p ≡ frontEndToGRU p
canonicalFrontEndToGRU p = refl

canonicalDPGGreedyTarget :
  ∀ (reward : ℕ) (δ : ℕ → ℕ) (q : Q) (π : GreedyPolicy) →
  IsGreedy π q →
  ∀ s → greedyPolicyBootstrap reward δ q π s ≡ maxQBootstrap reward δ q s
canonicalDPGGreedyTarget = DPG-maxQ-bootstrap-equivalence

canonicalHaarOrthogonal :
  haar-columns-orthogonal
canonicalHaarOrthogonal = haar-columns-orthogonal

canonicalHaarLeftNorm :
  haar-column-left-norm
canonicalHaarLeftNorm = haar-column-left-norm

canonicalHaarRightNorm :
  haar-column-right-norm
canonicalHaarRightNorm = haar-column-right-norm

canonicalCommonPrefix :
  ∀ (b : SharedDPGBand) (p : Int8Pair) →
  commonPrefixThenHeads b p
  ≡
  ( sharedActor b (frontEndToGRU p)
  , sharedCritic b (frontEndToGRU p) )
canonicalCommonPrefix = commonPrefix-factorization

canonicalDiscretePQNTarget :
  ∀ (v : DiscretePQNVariant) (reward : ℕ) (δ : ℕ → ℕ) (q : Q) →
  ∀ s → discretePQNTarget v reward δ q s ≡ maxQBootstrap reward δ q s
canonicalDiscretePQNTarget = discretePQN-target-common

canonicalPromotedActor :
  ∀ (a : DPGActor) (x : Int8) → promotedDPGActor a x ≡ actorForward a x
canonicalPromotedActor = promotedDPGActor-total

canonicalPromotedActorOptimizer : promotedActorOptimizer
canonicalPromotedActorOptimizer = promotedActorOptimizer

canonicalPromotedActorL2 : promotedActorL2
canonicalPromotedActorL2 = promotedActorL2

canonicalPromotedCriticOptimizer : promotedCriticOptimizer
canonicalPromotedCriticOptimizer = promotedCriticOptimizer

canonicalPromotedCriticL2 : promotedCriticL2
canonicalPromotedCriticL2 = promotedCriticL2

canonicalPromotedActorPerturbation : promotedActor-under-perturbation
canonicalPromotedActorPerturbation = promotedActor-under-perturbation

canonicalPromotedCriticPerturbation : promotedCritic-under-perturbation
canonicalPromotedCriticPerturbation = promotedCritic-under-perturbation

canonicalPromotedComposition : promotedComposition-law
canonicalPromotedComposition = promotedComposition-law

canonicalPromotedCompositionActorOptimizer : promotedComposition-actor-optimizer
canonicalPromotedCompositionActorOptimizer = promotedComposition-actor-optimizer

canonicalPromotedCompositionActorL2 : promotedComposition-actor-L2
canonicalPromotedCompositionActorL2 = promotedComposition-actor-L2

canonicalPromotedCompositionCriticOptimizer : promotedComposition-critic-optimizer
canonicalPromotedCompositionCriticOptimizer = promotedComposition-critic-optimizer

canonicalPromotedCompositionCriticL2 : promotedComposition-critic-L2
canonicalPromotedCompositionCriticL2 = promotedComposition-critic-L2

canonicalPromotedGreedyTarget : promotedGreedyTarget
canonicalPromotedGreedyTarget = promotedGreedyTarget

------------------------------------------------------------------------
-- Watkins/DPG trace surface.
------------------------------------------------------------------------

canonicalWatkinsCut :
  ∀ (xs : List TraceDecision) →
  watkinsTraceLength (cutTrace ∷ xs) ≡ suc zero
canonicalWatkinsCut = watkinsTraceLength-cut-head

canonicalWatkinsEmpty : watkinsTraceLength [] ≡ zero
canonicalWatkinsEmpty = watkinsTraceLength-empty

canonicalWatkinsKeep :
  ∀ (xs : List TraceDecision) →
  watkinsTraceLength (keepTrace ∷ xs) ≡ suc (watkinsTraceLength xs)
canonicalWatkinsKeep = watkinsTraceLength-keep

canonicalWatkinsExploration :
  ∀ (e : WatkinsExploration) →
  sampledAction (watkinsCut e) ≡ sampledAction e
canonicalWatkinsExploration = watkinsCut-preserves-action

canonicalWatkinsActor :
  ∀ (a : DPGActor) (x : Int8) →
  actorForward a x ≡ actorForward a x
canonicalWatkinsActor a x = watkinsActorPreserved a x

canonicalWatkinsCritic :
  ∀ (c : DPGCritic) (x : Int8) →
  criticForward c x ≡ criticForward c x
canonicalWatkinsCritic c x = watkinsCriticPreserved c x

canonicalWatkinsAllCuts :
  ∀ n → watkinsTraceLength (allCuts (suc n)) ≡ suc zero
canonicalWatkinsAllCuts = allCuts-length-suc

canonicalWatkinsOneStep : watkinsTraceLength (cutTrace ∷ []) ≡ suc zero
canonicalWatkinsOneStep = watkins-one-step-under-cut

canonicalWatkinsDPGStep :
  ∀ (c : DPGCritic) (a : DPGActor) (x : Int8) →
  dpgWatkinsCriticStep c a x ≡ criticForward c (actorForward a x)
canonicalWatkinsDPGStep = dpgWatkinsCriticStep-law

canonicalWatkinsCutRegime :
  ∀ xs → watkinsRegime (cutTrace ∷ xs) ≡ oneStep
canonicalWatkinsCutRegime = cut-regime-is-one-step
