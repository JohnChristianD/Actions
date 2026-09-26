{-
  Proof-only e-graph semantic transport.

  This module does not implement an e-graph data structure and does not
  manufacture any physical witness. It gives the existing commuting-square
  architecture a small semantic interface: an e-graph congruence is sound
  when its related expressions have equal interpretations. Once that
  semantic equality is available, ordinary Agda congruence transports it
  through the existing learner/physical maps.

  The intended use is to connect symbolic equality-saturation artifacts to
  the canonical theorem layer without treating graph membership as a proof
  of a physical law.
-}

{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.EGraphSemanticTransport where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.List using (List)

------------------------------------------------------------------------
-- Abstract e-graph congruence.
------------------------------------------------------------------------

record EGraphCongruence (Expression : Set) : Set₁ where
  constructor eGraphCongruence
  field
    related : Expression → Expression → Set

    related-refl :
      ∀ e →
      related e e

    related-sym :
      ∀ {e f} →
      related e f →
      related f e

    related-trans :
      ∀ {e f g} →
      related e f →
      related f g →
      related e g

open EGraphCongruence public

------------------------------------------------------------------------
-- Semantic interpretation of an e-graph congruence.
--
-- Soundness is the only bridge required here: graph equivalence is not
-- silently identified with definitional equality.
------------------------------------------------------------------------

record EGraphSemanticInterpretation
  (Expression State : Set) : Set₁ where
  constructor eGraphSemanticInterpretation
  field
    congruence : EGraphCongruence Expression
    interpret : Expression → State
    sound :
      ∀ {e f} →
      related congruence e f →
      interpret e ≡ interpret f

open EGraphSemanticInterpretation public

data SemanticEdgeStatus : Set where
  semanticProved
  semanticConditional
  semanticFrontier
  semanticBlockedByCounterexample :
  SemanticEdgeStatus

data SemanticEdgeEvidence : Set where
  kernelProof
  discoveryArtifact
  externalLiterature :
  SemanticEdgeEvidence

record SemanticEdgeMetadata : Set₁ where
  constructor semanticEdgeMetadata
  field
    source : String
    target : String
    proofIdentifier : String
    assumptions : List String
    status : SemanticEdgeStatus
    evidence : SemanticEdgeEvidence
    unconditional : Bool

record CertifiedEGraphEdge
  {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State)
  (lhs rhs : Expression) : Set₁ where
  constructor certifiedEGraphEdge
  field
    metadata : SemanticEdgeMetadata
    path : EGraphSemanticPath R lhs rhs

eGraph-certified-edge-sound :
  ∀ {Expression State : Set}
  {R : EGraphSemanticInterpretation Expression State}
  {lhs rhs : Expression} →
  CertifiedEGraphEdge R lhs rhs →
  interpret R lhs ≡ interpret R rhs
eGraph-certified-edge-sound edge =
  eGraph-path-sound _ (path edge)

------------------------------------------------------------------------
-- Basic semantic closure of graph equivalence.
------------------------------------------------------------------------

eGraph-sound-refl :
  ∀ {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State) →
  ∀ e →
  interpret R e ≡ interpret R e
eGraph-sound-refl R e = refl

eGraph-sound-sym :
  ∀ {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State)
  {e f : Expression} →
  related (congruence R) e f →
  interpret R f ≡ interpret R e
eGraph-sound-sym R h = sym (sound R h)

eGraph-sound-trans :
  ∀ {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State)
  {e f g : Expression} →
  related (congruence R) e f →
  related (congruence R) f g →
  interpret R e ≡ interpret R g
eGraph-sound-trans R h₁ h₂ =
  trans (sound R h₁) (sound R h₂)

------------------------------------------------------------------------
-- Contextual transport.
--
-- If a state transformation is a semantic context, e-graph equality can
-- be pushed through it by ordinary equality congruence. This is the
-- semantic kernel consumed by commuting-square and iterate/prefix proofs.
------------------------------------------------------------------------

eGraph-context :
  ∀ {Expression State Context : Set}
  (R : EGraphSemanticInterpretation Expression State)
  (context : State → Context) →
  ∀ {e f : Expression} →
  related (congruence R) e f →
  context (interpret R e) ≡ context (interpret R f)
eGraph-context R context h =
  cong context (sound R h)

eGraph-rewrite-context :
  ∀ {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State)
  (step : State → State) →
  ∀ {e f : Expression} →
  related (congruence R) e f →
  step (interpret R e) ≡ step (interpret R f)
eGraph-rewrite-context R step h =
  cong step (sound R h)

------------------------------------------------------------------------
-- The semantic e-graph contract is deliberately proof-only. It closes
-- graph-level equality transport, while the concrete Law I/Law III and
-- physics-to-learner witness records remain separate obligations.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Cost-guided e-graph paths.
--
-- A* is a search strategy, not a proof rule.  The semantic proof is the
-- path of sound e-graph edges; the Nat cost is carried separately so an
-- A*-style selector can optimize traversal without changing the proof.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

record AStarCostModel (Expression : Set) : Set₁ where
  constructor aStarCostModel
  field
    edgeCost : Expression → Expression → Nat
    heuristic : Expression → Nat

open AStarCostModel public

data EGraphSemanticPath
  {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State) :
  Expression → Expression → Set where
  path-refl :
    ∀ e →
    EGraphSemanticPath R e e
  path-step :
    ∀ {e f g} →
    related (congruence R) e f →
    EGraphSemanticPath R f g →
    EGraphSemanticPath R e g

eGraph-path-sound :
  ∀ {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State) →
  ∀ {e f} →
  EGraphSemanticPath R e f →
  interpret R e ≡ interpret R f
eGraph-path-sound R (path-refl e) = refl
eGraph-path-sound R (path-step h rest) =
  trans (sound R h) (eGraph-path-sound R rest)

record AStarSemanticClosure
  (Expression State : Set) : Set₁ where
  constructor aStarSemanticClosure
  field
    semantics : EGraphSemanticInterpretation Expression State
    costs : AStarCostModel Expression

open AStarSemanticClosure public

aStar-guided-semantic-closure :
  ∀ {Expression State : Set}
  (A : AStarSemanticClosure Expression State) →
  ∀ {e f : Expression} →
  EGraphSemanticPath (semantics A) e f →
  interpret (semantics A) e ≡ interpret (semantics A) f
aStar-guided-semantic-closure A =
  eGraph-path-sound (semantics A)

------------------------------------------------------------------------
-- The cost/heuristic fields are intentionally not used in the equality
-- proof.  This prevents A* from becoming an unsound source of semantic
-- equality while still giving the discovery layer a typed cost-guidance
-- object that can be attached to a sound e-graph interpretation.
------------------------------------------------------------------------
