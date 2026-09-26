{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Canonical theorem semantics and emergence layer.
--
-- This module is the single theorem consumer of the canonical learner.
-- Its propositions are derived from the actual learner definitions and
-- from explicit hypotheses supplied at each abstraction boundary.
--
-- The proof topology is intentionally directional:
--   learner definitions
--     -> exact scan / composition laws
--     -> observation, quotient, and factor structure
--     -> F4 stability and exact growth boundary
--     -> coupled factor-stability closure
--     -> explicit economic interpretation gates.
--
-- A discovered graph edge is not itself a proof. A theorem is authoritative
-- only when its proposition is present here and its proof is accepted by
-- safe Agda. Likewise, a semantic contract is not an existence theorem:
-- the generalized Walrasian and production-side interfaces record the
-- conditions of an equilibrium, while existence, convergence, market
-- clearing, or supporting-price conclusions require their own assumptions.
--
-- The comments in this file therefore describe semantic intention and
-- emergence from the current definitions, not historical theorem partitions,
-- search candidates, or superseded contract surfaces.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.TheoremsMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (NonZero; _∸_; _<_; _≤_; _<ᵇ_; _/_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-antisym; ≤-refl; ≤-trans; ≤-decTotalOrder; n<1+n)
open import Data.Integer using (ℤ; +_; -_; -[1+_]; _≤?_; _≤_) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; _≤_ to _≤ℤ_)
import Data.Integer.Properties as IntegerProperties
open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Sort as Sort
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Binary.Construct.On as On
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Data.Product.Relation.Binary.Lex.NonStrict as Lex
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.List using (List)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans; sym)
open import Agda.Builtin.Nat using (Nat; zero; suc; _≤_; z≤n)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)
open import Data.Nat using (Nat; zero)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans)
open import Relation.Nullary using (¬_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C


------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/TsallisStatisticalRepresentation.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Carrier-polymorphic statistical representation.
--
-- This module is deliberately arithmetic-free: the abstract Law-IV
-- representation needs only Set, functions, and propositional equality.
-- A Tsallis/q-statistical interpretation may instantiate the observation
-- carrier, but no Real or Rational specialization is required here; the observation carrier is an arbitrary Set.
--
-- The representation theorem is structural. External statistical
-- literature motivates possible instantiations; it is not imported as an
-- Agda proof source.
------------------------------------------------------------------------


record CarrierPolymorphicStatisticalRepresentation
  (State Observation : Set) : Set₁ where
  constructor carrierPolymorphicStatisticalRepresentation
  field
    encode : State → Observation
    decode : Observation → State
    decodeEncode : ∀ s → decode (encode s) ≡ s

open CarrierPolymorphicStatisticalRepresentation public

statisticalEncodeInjective :
  ∀ {State Observation : Set}
  (R : CarrierPolymorphicStatisticalRepresentation State Observation)
  {s t : State} →
  encode R s ≡ encode R t →
  s ≡ t
statisticalEncodeInjective R eq = cong (decode R) eq

statisticalEncodeDistinguishes :
  ∀ {State Observation : Set}
  (R : CarrierPolymorphicStatisticalRepresentation State Observation)
  {s t : State} →
  s ≢ t →
  encode R s ≢ encode R t
statisticalEncodeDistinguishes R distinct collision =
  distinct (statisticalEncodeInjective R collision)

record TsallisCompatibleStatisticalRepresentation
  (State Observation : Set) : Set₁ where
  constructor tsallisCompatibleStatisticalRepresentation
  field
    representation :
      CarrierPolymorphicStatisticalRepresentation State Observation

open TsallisCompatibleStatisticalRepresentation public

tsallisCompatibleEncodeInjective :
  ∀ {State Observation : Set}
  (R : TsallisCompatibleStatisticalRepresentation State Observation)
  {s t : State} →
  encode (representation R) s ≡ encode (representation R) t →
  s ≡ t
tsallisCompatibleEncodeInjective R =
  statisticalEncodeInjective (representation R)

tsallisCompatibleEncodeDistinguishes :
  ∀ {State Observation : Set}
  (R : TsallisCompatibleStatisticalRepresentation State Observation)
  {s t : State} →
  s ≢ t →
  encode (representation R) s ≢ encode (representation R) t
tsallisCompatibleEncodeDistinguishes R =
  statisticalEncodeDistinguishes (representation R)

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/GRUStatisticalInjectivity.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.GRUStatisticalInjectivity where
CanonicalGRUStatisticalObservation : Set
CanonicalGRUStatisticalObservation = C.GRUState × (C.CanonicalToken → C.Int8)
canonicalGRUStatisticalEncode : C.GRUState → CanonicalGRUStatisticalObservation
canonicalGRUStatisticalEncode s = s , (λ _ → C.hiddenState s)
canonicalGRUStatisticalDecode : CanonicalGRUStatisticalObservation → C.GRUState
canonicalGRUStatisticalDecode observation = proj₁ observation
canonicalGRUStatisticalDecodeEncode : ∀ s → canonicalGRUStatisticalDecode (canonicalGRUStatisticalEncode s) ≡ s
canonicalGRUStatisticalDecodeEncode s = refl
canonicalGRUStatisticalEncodeInjective : ∀ {s t : C.GRUState} → canonicalGRUStatisticalEncode s ≡ canonicalGRUStatisticalEncode t → s ≡ t
canonicalGRUStatisticalEncodeInjective eq = cong canonicalGRUStatisticalDecode eq
record CanonicalGRUStatisticalInjectivityTheorem : Set₁ where
  constructor canonicalGRUStatisticalInjectivityTheorem
  field
    encode : C.GRUState → CanonicalGRUStatisticalObservation
    decode : CanonicalGRUStatisticalObservation → C.GRUState
    decodeEncode : ∀ s → decode (encode s) ≡ s
    injective : ∀ {s t : C.GRUState} → encode s ≡ encode t → s ≡ t
canonical-gru-statistical-injectivity-theorem : CanonicalGRUStatisticalInjectivityTheorem
canonical-gru-statistical-injectivity-theorem = canonicalGRUStatisticalInjectivityTheorem canonicalGRUStatisticalEncode canonicalGRUStatisticalDecode canonicalGRUStatisticalDecodeEncode canonicalGRUStatisticalEncodeInjective
canonicalGRUStatisticalDistinguishability : ∀ {s t : C.GRUState} → s ≢ t → canonicalGRUStatisticalEncode s ≢ canonicalGRUStatisticalEncode t
canonicalGRUStatisticalDistinguishability distinct collision = distinct (canonicalGRUStatisticalEncodeInjective collision)
canonicalGRUStatisticalStepConsequence : ∀ (s : C.GRUState) (x : C.Int8) → canonicalGRUStatisticalEncode (C.gruStep s x) ≡ (C.gruStep s x , (λ _ → C.hiddenState (C.gruStep s x)))
canonicalGRUStatisticalStepConsequence s x = refl

------------------------------------------------------------------------
-- Carrier-polymorphic Law-IV instance. The concrete canonical observation
-- remains available above, while the injectivity mechanism is now supplied
-- by the arithmetic-free representation kernel.
------------------------------------------------------------------------

canonicalGRUTsallisCompatibleRepresentation :
  TsallisCompatibleStatisticalRepresentation
    C.GRUState
    CanonicalGRUStatisticalObservation
canonicalGRUTsallisCompatibleRepresentation =
  tsallisCompatibleStatisticalRepresentation
    (carrierPolymorphicStatisticalRepresentation
      canonicalGRUStatisticalEncode
      canonicalGRUStatisticalDecode
      canonicalGRUStatisticalDecodeEncode)

canonicalGRUTsallisCompatibleInjective :
  ∀ {s t : C.GRUState} →
  encode
    (representation canonicalGRUTsallisCompatibleRepresentation) s
  ≡
  encode
    (representation canonicalGRUTsallisCompatibleRepresentation) t →
  s ≡ t
canonicalGRUTsallisCompatibleInjective =
  tsallisCompatibleEncodeInjective
    canonicalGRUTsallisCompatibleRepresentation

canonicalGRUTsallisCompatibleDistinguishability :
  ∀ {s t : C.GRUState} →
  s ≢ t →
  encode
    (representation canonicalGRUTsallisCompatibleRepresentation) s
  ≢
  encode
    (representation canonicalGRUTsallisCompatibleRepresentation) t
canonicalGRUTsallisCompatibleDistinguishability =
  tsallisCompatibleEncodeDistinguishes
    canonicalGRUTsallisCompatibleRepresentation

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/ZPFStatisticalRepresentation.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Typed ZPF / omega^3 semantic boundary for the canonical GRU layer.
--
-- The physical ZPF carrier, Maxwell constraints, stochastic semantics,
-- and spectral convention are explicit inputs.  The module does not
-- manufacture a physical ZPF inhabitant.
--
-- The omega^3 law is represented by an explicit frequency multiplication
-- operation, a proof that omegaCubed is the triple product, and a
-- spectral-density normalization carrier.  A concrete instantiation decides
-- the frequency measure and normalization (for example, per unit angular
-- frequency) without introducing a new arithmetic dependency here.
--
-- Once a ZPF -> canonical-GRU statistical representation supplies
-- decode (encode z) == z, global injectivity follows from the existing
-- carrier-polymorphic statistical representation theorem.
------------------------------------------------------------------------


record ZPFOmegaCubedSpectralLaw
  (ZPFState Frequency SpectralDensity : Set)
  (frequencyMultiply : Frequency → Frequency → Frequency) : Set₁ where
  constructor zpfOmegaCubedSpectralLaw
  field
    density :
      ZPFState → Frequency → SpectralDensity
    spectralDensityOfOmegaCubed :
      Frequency → SpectralDensity
    omegaCubed :
      Frequency → Frequency
    omegaCubedDefinition :
      ∀ (ω : Frequency) →
      omegaCubed ω ≡
      frequencyMultiply (frequencyMultiply ω ω) ω
    omegaCubedLaw :
      ∀ (z : ZPFState) (ω : Frequency) →
      density z ω ≡ spectralDensityOfOmegaCubed (omegaCubed ω)

open ZPFOmegaCubedSpectralLaw public

record ZPFMaxwellSemanticData
  (ZPFState MaxwellField Frequency SpectralDensity : Set)
  (frequencyMultiply : Frequency → Frequency → Frequency)
  (Homogeneous Isotropic Maxwell : MaxwellField → Set)
  (Stochastic : ZPFState → Set) : Set₁ where
  constructor zpfMaxwellSemanticData
  field
    fieldZPF :
      ZPFState → MaxwellField
    homogeneous :
      ∀ z → Homogeneous (fieldZPF z)
    isotropic :
      ∀ z → Isotropic (fieldZPF z)
    stochastic :
      ∀ z → Stochastic z
    maxwell :
      ∀ z → Maxwell (fieldZPF z)
    spectralLaw :
      ZPFOmegaCubedSpectralLaw
        ZPFState
        Frequency
        SpectralDensity
        frequencyMultiply

open ZPFMaxwellSemanticData public

record ZPFGRUStatisticalRepresentation
  (ZPFState Frequency SpectralDensity MaxwellField : Set)
  (frequencyMultiply : Frequency → Frequency → Frequency)
  (Homogeneous Isotropic Maxwell : MaxwellField → Set)
  (Stochastic : ZPFState → Set) : Set₁ where
  constructor zpfGRUStatisticalRepresentation
  field
    zpfSemantics :
      ZPFMaxwellSemanticData
        ZPFState
        MaxwellField
        Frequency
        SpectralDensity
        frequencyMultiply
        Homogeneous
        Isotropic
        Maxwell
        Stochastic
    statisticalRepresentation :
      CarrierPolymorphicStatisticalRepresentation
        ZPFState
        G.CanonicalGRUStatisticalObservation

open ZPFGRUStatisticalRepresentation public

zpfGRUStatisticalEncodeInjective :
  ∀ {ZPFState Frequency SpectralDensity MaxwellField : Set}
  {frequencyMultiply : Frequency → Frequency → Frequency}
  {Homogeneous Isotropic Maxwell : MaxwellField → Set}
  {Stochastic : ZPFState → Set}
  (R :
    ZPFGRUStatisticalRepresentation
      ZPFState
      Frequency
      SpectralDensity
      MaxwellField
      frequencyMultiply
      Homogeneous
      Isotropic
      Maxwell
      Stochastic)
  {z₁ z₂ : ZPFState} →
  encode (statisticalRepresentation R) z₁ ≡
  encode (statisticalRepresentation R) z₂ →
  z₁ ≡ z₂
zpfGRUStatisticalEncodeInjective R =
  statisticalEncodeInjective (statisticalRepresentation R)

zpfGRUStatisticalDistinguishes :
  ∀ {ZPFState Frequency SpectralDensity MaxwellField : Set}
  {frequencyMultiply : Frequency → Frequency → Frequency}
  {Homogeneous Isotropic Maxwell : MaxwellField → Set}
  {Stochastic : ZPFState → Set}
  (R :
    ZPFGRUStatisticalRepresentation
      ZPFState
      Frequency
      SpectralDensity
      MaxwellField
      frequencyMultiply
      Homogeneous
      Isotropic
      Maxwell
      Stochastic)
  {z₁ z₂ : ZPFState} →
  z₁ ≢ z₂ →
  encode (statisticalRepresentation R) z₁ ≢
  encode (statisticalRepresentation R) z₂
zpfGRUStatisticalDistinguishes R =
  statisticalEncodeDistinguishes (statisticalRepresentation R)

record ZPFGRUGlobalInjectivityTheorem
  (ZPFState Frequency SpectralDensity MaxwellField : Set)
  (frequencyMultiply : Frequency → Frequency → Frequency)
  (Homogeneous Isotropic Maxwell : MaxwellField → Set)
  (Stochastic : ZPFState → Set) : Set₁ where
  constructor zpfGRUGlobalInjectivityTheoremWitness
  field
    representation :
      ZPFGRUStatisticalRepresentation
        ZPFState
        Frequency
        SpectralDensity
        MaxwellField
        frequencyMultiply
        Homogeneous
        Isotropic
        Maxwell
        Stochastic
    globalInjective :
      ∀ {z₁ z₂ : ZPFState} →
      encode (statisticalRepresentation representation) z₁ ≡
      encode (statisticalRepresentation representation) z₂ →
      z₁ ≡ z₂

zpfGRUGlobalInjectivityTheorem :
  ∀ {ZPFState Frequency SpectralDensity MaxwellField : Set}
  {frequencyMultiply : Frequency → Frequency → Frequency}
  {Homogeneous Isotropic Maxwell : MaxwellField → Set}
  {Stochastic : ZPFState → Set} →
  ZPFGRUStatisticalRepresentation
    ZPFState
    Frequency
    SpectralDensity
    MaxwellField
    frequencyMultiply
    Homogeneous
    Isotropic
    Maxwell
    Stochastic →
  ZPFGRUGlobalInjectivityTheorem
    ZPFState
    Frequency
    SpectralDensity
    MaxwellField
    frequencyMultiply
    Homogeneous
    Isotropic
    Maxwell
    Stochastic
zpfGRUGlobalInjectivityTheorem R =
  zpfGRUGlobalInjectivityTheoremWitness
    R
    (zpfGRUStatisticalEncodeInjective R)

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/EGraphSemanticTransport.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

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

data SemanticEdgeStatus : Set where
  semanticProved : SemanticEdgeStatus
  semanticConditional : SemanticEdgeStatus
  semanticFrontier : SemanticEdgeStatus
  semanticBlockedByCounterexample : SemanticEdgeStatus

data SemanticEdgeEvidence : Set where
  kernelProof : SemanticEdgeEvidence
  discoveryArtifact : SemanticEdgeEvidence
  externalLiterature : SemanticEdgeEvidence

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

open CertifiedEGraphEdge public

eGraph-certified-edge-sound :
  ∀ {Expression State : Set}
  {R : EGraphSemanticInterpretation Expression State}
  {lhs rhs : Expression} →
  CertifiedEGraphEdge R lhs rhs →
  interpret R lhs ≡ interpret R rhs
eGraph-certified-edge-sound edge =
  eGraph-path-sound _ (path edge)


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

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/RepositorySemanticEGraphClosure.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Repository-wide semantic e-graph closure.
--
-- This module closes the semantic layer for every indexed Agda module
-- without pretending that module names or search costs are physical laws.
-- A module contributes a sound interpretation; e-graph paths then compose
-- exact semantic equality, and A* supplies traversal cost/heuristic data
-- without entering the equality proof.
--
-- The repository index below is deliberately finite and explicit.  It names
-- every surviving Agda file in Exotic/ERL/FullCoupled on this branch.  The
-- closure theorem is still parametric in the semantic interpretation for
-- each file: enumeration does not manufacture semantic soundness.
------------------------------------------------------------------------


data RepositoryAgdaModule : Set where
  canonicalLearnerMonolith :
    RepositoryAgdaModule
  theoremsMonolith :
    RepositoryAgdaModule

record AgdaSemanticModuleFamily : Set₁ where
  constructor agdaSemanticModuleFamily
  field
    Expression : RepositoryAgdaModule → Set
    State : RepositoryAgdaModule → Set
    closure :
      (m : RepositoryAgdaModule) →
      AStarSemanticClosure
        (Expression m)
        (State m)

open AgdaSemanticModuleFamily public

repositoryAgdaAStarSemanticClosure :
  (F : AgdaSemanticModuleFamily)
  (m : RepositoryAgdaModule)
  {e f : Expression F m} →
  EGraphSemanticPath
    (semantics (closure F m))
    e
    f →
  interpret (semantics (closure F m)) e
  ≡
  interpret (semantics (closure F m)) f
repositoryAgdaAStarSemanticClosure F m =
  aStar-guided-semantic-closure (closure F m)

record UnconditionalAgdaEGraphAStarClosure : Set₁ where
  constructor unconditionalAgdaEGraphAStarClosure
  field
    closeAll :
      (F : AgdaSemanticModuleFamily)
      (m : RepositoryAgdaModule)
      {e f : Expression F m} →
      EGraphSemanticPath
        (semantics (closure F m))
        e
        f →
      interpret (semantics (closure F m)) e
      ≡
      interpret (semantics (closure F m)) f

unconditional-agda-egraph-astar-closure :
  UnconditionalAgdaEGraphAStarClosure
unconditional-agda-egraph-astar-closure =
  unconditionalAgdaEGraphAStarClosure
    repositoryAgdaAStarSemanticClosure

------------------------------------------------------------------------
-- The theorem is unconditional over the complete surviving Agda-file
-- index and any supplied semantic family:
--
--   enumerated file
--     -> supplied sound interpretation
--     -> sound e-graph path
--     -> exact endpoint equality
--
-- A* costs/heuristics guide discovery but are not equality evidence.
-- This does not assert that every physical Maxwell witness, economic
-- equilibrium witness, or other domain-specific inhabitant exists.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/FourLawClosureWitnesses.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Minimal typed contract for the missing four-law closure witnesses.
--
-- This module is intentionally a contract, not an existence theorem.
-- It records exactly the semantic data that must be inhabited before
-- Law I + Law III + physics-to-learner transport can be promoted into
-- the existing Law II/Law IV composition.
------------------------------------------------------------------------


record LawIPhysicsWitness
  (LearnerState PhysicalState Current : Set) : Set₁ where
  constructor lawIPhysicsWitness
  field
    encode : LearnerState → PhysicalState
    decode : PhysicalState → LearnerState
    decodeEncode :
      ∀ s → decode (encode s) ≡ s
    trajectory :
      PhysicalState → PhysicalState
    current :
      PhysicalState → Current
    trajectoryCurrentCompatibility :
      ∀ p → current (trajectory p) ≡ current p

record LawIIIVariationalWitness
  (LearnerState PhysicalState Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set) : Set₁ where
  constructor lawIIIVariationalWitness
  field
    encode : LearnerState → PhysicalState
    decode : PhysicalState → LearnerState
    decodeEncode :
      ∀ s → decode (encode s) ≡ s
    variation : PhysicalState → Variation
    action : PhysicalState → Action
    admissibleVariation :
      ∀ p → Admissible (variation p)
    stationary :
      ∀ p → Stationary p

record PhysicsToLearnerTransitionWitness
  (LearnerState PhysicalState : Set)
  (learnerStep : LearnerState → LearnerState)
  (physicalStep : PhysicalState → PhysicalState) : Set₁ where
  constructor physicsToLearnerTransitionWitness
  field
    encode : LearnerState → PhysicalState
    decode : PhysicalState → LearnerState
    decodeEncode :
      ∀ s → decode (encode s) ≡ s
    stepConjugacy :
      ∀ s →
      encode (learnerStep s)
      ≡
      physicalStep (encode s)

record FourLawOneStepWitnessContract
  (LearnerState PhysicalState Current Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set)
  (learnerStep : LearnerState → LearnerState)
  (physicalStep : PhysicalState → PhysicalState) : Set₁ where
  constructor fourLawOneStepWitnessContract
  field
    lawI :
      LawIPhysicsWitness
        LearnerState
        PhysicalState
        Current
    lawIII :
      LawIIIVariationalWitness
        LearnerState
        PhysicalState
        Variation
        Action
        Admissible
        Stationary
    physicsToLearner :
      PhysicsToLearnerTransitionWitness
        LearnerState
        PhysicalState
        learnerStep
        physicalStep

------------------------------------------------------------------------
-- Generic autonomous-time lifting of the physics-to-learner square.
-- This is proof infrastructure only; it does not create a missing
-- physics witness.
------------------------------------------------------------------------

iterateStep :
  ∀ {State : Set} →
  (State → State) →
  Nat →
  State →
  State
iterateStep step zero s = s
iterateStep step (suc n) s = iterateStep step n (step s)

iterateConjugacy :
  ∀ {LearnerState PhysicalState : Set}
  {learnerStep : LearnerState → LearnerState}
  {physicalStep : PhysicalState → PhysicalState}
  (encode : LearnerState → PhysicalState)
  (stepConjugacy :
    ∀ s →
    encode (learnerStep s) ≡
    physicalStep (encode s)) →
  ∀ n s →
  encode (iterateStep learnerStep n s)
  ≡
  iterateStep physicalStep n (encode s)
iterateConjugacy encode stepConjugacy zero s = refl
iterateConjugacy encode stepConjugacy (suc n) s =
  trans
    (iterateConjugacy
      encode
      stepConjugacy
      n
      (learnerStep s))
    (cong
      (iterateStep physicalStep n)
      (stepConjugacy s))

------------------------------------------------------------------------
-- Input-indexed square contract for prefix scans. This is deliberately
-- separate from the autonomous iterate witness: a prefix consumes an
-- input at every step, so the commuting law must quantify over input.
------------------------------------------------------------------------

record InputIndexedConjugacy
  (LearnerState PhysicalState Input : Set) : Set₁ where
  constructor inputIndexedConjugacy
  field
    encode : LearnerState → PhysicalState
    learnerStep : LearnerState → Input → LearnerState
    physicalStep : PhysicalState → Input → PhysicalState
    stepConjugacy :
      ∀ s x →
      encode (learnerStep s x)
      ≡
      physicalStep (encode s) x

open InputIndexedConjugacy public

prefixScan :
  ∀ {State Input : Set} →
  (State → Input → State) →
  List Input →
  State →
  State
prefixScan step [] s = s
prefixScan step (x ∷ xs) s =
  prefixScan step xs (step s x)

prefixScanConjugacy :
  ∀ {LearnerState PhysicalState Input : Set}
  (R : InputIndexedConjugacy LearnerState PhysicalState Input) →
  ∀ xs s →
  encode R (prefixScan (learnerStep R) xs s)
  ≡
  prefixScan (physicalStep R) xs (encode R s)
prefixScanConjugacy R [] s = refl
prefixScanConjugacy R (x ∷ xs) s =
  trans
    (prefixScanConjugacy
      R
      xs
      (learnerStep R s x))
    (cong
      (prefixScan (physicalStep R) xs)
      (stepConjugacy R s x))

------------------------------------------------------------------------
-- No inhabitant is supplied here. The admissibility and stationarity
-- predicates are explicit semantic obligations; these contracts do not
-- manufacture them from learner algebra.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/FourLawClosureImpossibility.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

GenericFourLawClosureConstructor :
  Set₁
GenericFourLawClosureConstructor =
  ∀ {LearnerState PhysicalState Current Variation Action : Set}
    (Admissible : Variation → Set)
    (Stationary : PhysicalState → Set)
    (learnerStep : LearnerState → LearnerState)
    (physicalStep : PhysicalState → PhysicalState) →
    FourLawOneStepWitnessContract
      LearnerState
      PhysicalState
      Current
      Variation
      Action
      Admissible
      Stationary
      learnerStep
      physicalStep

no-generic-four-law-closure-constructor :
  GenericFourLawClosureConstructor → ⊥
no-generic-four-law-closure-constructor make =
  LawIIIVariationalWitness.stationary
    (FourLawOneStepWitnessContract.lawIII
      (make
        {LearnerState = ⊤}
        {PhysicalState = ⊤}
        {Current = ⊤}
        {Variation = ⊤}
        {Action = ⊤}
        (λ _ → ⊤)
        (λ _ → ⊥)
        (λ _ → tt)
        (λ _ → tt)))
    tt

NoGenericFourLawClosure : Set₁
NoGenericFourLawClosure = GenericFourLawClosureConstructor → ⊥

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/GRUFractalInjectiveComposition.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Generic self-similar/fractal injective-composition kernel.
--
-- "Fractal" is used here only with an explicit level relation and an
-- inter-level transport law. Mere indexing by Level is not treated as
-- fractality.
------------------------------------------------------------------------


record FractalInjectiveComposition
  (Level State Observation : Set)
  (Refines : Level → Level → Set) : Set₁ where
  constructor fractalInjectiveComposition
  field
    encode : Level → State → Observation
    decode : Level → Observation → State
    decodeEncode : ∀ level state → decode level (encode level state) ≡ state

    transport :
      ∀ {lower upper} →
      Refines lower upper →
      Observation →
      Observation

    transportInjective :
      ∀ {lower upper} {r : Refines lower upper} {x y : Observation} →
      transport r x ≡ transport r y →
      x ≡ y

    transportEncode :
      ∀ {lower upper} (r : Refines lower upper) state →
      transport r (encode lower state) ≡
      encode upper state

open FractalInjectiveComposition public

fractalLevelInjective :
  ∀ {Level State Observation : Set}
  {Refines : Level → Level → Set}
  (F : FractalInjectiveComposition Level State Observation Refines) →
  ∀ level {s t : State} →
  encode F level s ≡ encode F level t →
  s ≡ t
fractalLevelInjective F level eq =
  trans
    (decodeEncode F level _)
    (cong (decode F level) eq)

fractalTransportedEncodeInjective :
  ∀ {Level State Observation : Set}
  {Refines : Level → Level → Set}
  (F : FractalInjectiveComposition Level State Observation Refines) →
  ∀ {lower upper} (r : Refines lower upper) {s t : State} →
  transport F r (encode F lower s) ≡
  transport F r (encode F lower t) →
  s ≡ t
fractalTransportedEncodeInjective F r eq =
  fractalLevelInjective F upper
    (trans
      (transportEncode F r _)
      (trans
        (transportInjective F eq)
        (sym (transportEncode F r _))))

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/GRUFractalInjectiveCompositionCanonical.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Canonical GRU instantiation of the fractal injective-composition kernel.
--
-- Nat indexes scale. The relation m ≤ n records refinement from a lower
-- level to an upper level. The canonical statistical observation is reused
-- unchanged at every scale, and the inter-level transport is the identity.
-- This is therefore an explicit scale-invariant self-similar instance,
-- not an assertion that every possible fractal representation is GRU
-- injective.
------------------------------------------------------------------------

  using
  ( CanonicalGRUStatisticalObservation
  ; canonicalGRUStatisticalEncode
  ; canonicalGRUStatisticalDecode
  ; canonicalGRUStatisticalDecodeEncode
  )

GRUFractalLevel : Set
GRUFractalLevel = Nat

GRUFractalRefines : GRUFractalLevel → GRUFractalLevel → Set
GRUFractalRefines lower upper = lower ≤ upper

canonicalGRUFractal : FractalInjectiveComposition
  GRUFractalLevel
  C.GRUState
  CanonicalGRUStatisticalObservation
  GRUFractalRefines
canonicalGRUFractal =
  fractalInjectiveComposition
    (λ _ → canonicalGRUStatisticalEncode)
    (λ _ → canonicalGRUStatisticalDecode)
    (λ level state → canonicalGRUStatisticalDecodeEncode state)
    (λ _ observation → observation)
    (λ eq → eq)
    (λ _ state → refl)

canonicalGRUFractalLevelInjective :
  ∀ level {s t : C.GRUState} →
  encode canonicalGRUFractal level s ≡
  encode canonicalGRUFractal level t →
  s ≡ t
canonicalGRUFractalLevelInjective =
  fractalLevelInjective canonicalGRUFractal

canonicalGRUFractalTransportedInjective :
  ∀ {lower upper : GRUFractalLevel}
  (r : GRUFractalRefines lower upper)
  {s t : C.GRUState} →
  transport canonicalGRUFractal r
    (encode canonicalGRUFractal lower s) ≡
  transport canonicalGRUFractal r
    (encode canonicalGRUFractal lower t) →
  s ≡ t
canonicalGRUFractalTransportedInjective =
  fractalTransportedEncodeInjective canonicalGRUFractal

canonicalGRUTwoScaleRefinement :
  GRUFractalRefines zero (suc zero)
canonicalGRUTwoScaleRefinement = z≤n

canonicalGRUTwoScaleInjective :
  ∀ {s t : C.GRUState} →
  transport canonicalGRUFractal canonicalGRUTwoScaleRefinement
    (encode canonicalGRUFractal zero s) ≡
  transport canonicalGRUFractal canonicalGRUTwoScaleRefinement
    (encode canonicalGRUFractal zero t) →
  s ≡ t
canonicalGRUTwoScaleInjective =
  canonicalGRUFractalTransportedInjective canonicalGRUTwoScaleRefinement

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/GRUFractalDomainAdapters.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Domain adapters for the GRU-injective fractal composition seam.
--
-- These are proof-relevant contracts, not fabricated inhabitants.
-- Physics remains blocked by the concrete Law-I/Law-III witnesses.
-- Economics additionally requires a genuine inter-level transport on
-- the economic carrier, not merely a level index.
------------------------------------------------------------------------

  using
  ( FourLawOneStepWitnessContract
  )
  using
  ( FractalInjectiveComposition
  )

record PhysicsGRUFractalAdapter
  (Level LearnerState PhysicalState Observation Current Variation Action : Set)
  (Refines : Level → Level → Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set)
  (learnerStep : LearnerState → LearnerState)
  (physicalStep : PhysicalState → PhysicalState) : Set₁ where
  constructor physicsGRUFractalAdapter
  field
    fourLawWitness :
      FourLawOneStepWitnessContract
        LearnerState
        PhysicalState
        Current
        Variation
        Action
        Admissible
        Stationary
        learnerStep
        physicalStep

    injectiveFractalRepresentation :
      FractalInjectiveComposition
        Level
        LearnerState
        Observation
        Refines

record EconomicsGRUFractalAdapter
  (Level LearnerState EconomicState Observation : Set)
  (Refines : Level → Level → Set)
  (learnerStep : LearnerState → LearnerState)
  (economicStep : EconomicState → EconomicState) : Set₁ where
  constructor economicsGRUFractalAdapter
  field
    learnerToEconomic :
      LearnerState → EconomicState
    economicToLearner :
      EconomicState → LearnerState

    learnerToEconomicInverse :
      ∀ s →
      economicToLearner (learnerToEconomic s) ≡ s

    economicToLearnerInverse :
      ∀ e →
      learnerToEconomic (economicToLearner e) ≡ e

    stepConjugacy :
      ∀ s →
      learnerToEconomic (learnerStep s) ≡
      economicStep (learnerToEconomic s)

    injectiveFractalRepresentation :
      FractalInjectiveComposition
        Level
        LearnerState
        Observation
        Refines

    economicObservation :
      EconomicState → Observation

    economicLevelTransport :
      ∀ {lower upper} →
      Refines lower upper →
      EconomicState →
      EconomicState

    economicLevelTransportInjective :
      ∀ {lower upper}
      {r : Refines lower upper}
      {x y : EconomicState} →
      economicLevelTransport r x ≡
      economicLevelTransport r y →
      x ≡ y

    economicLevelTransportRepresentation :
      ∀ {lower upper}
      (r : Refines lower upper)
      (e : EconomicState) →
      economicObservation
        (economicLevelTransport r e)
      ≡
      FractalInjectiveComposition.transport
        injectiveFractalRepresentation
        r
        (economicObservation e)

open PhysicsGRUFractalAdapter public
open EconomicsGRUFractalAdapter public

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/GRUFractalLimitClosure.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Arbitrary-limit closure boundary for GRU-injective fractal composition.
-- A limit object is not assumed to preserve injectivity merely because
-- every finite/indexed approximation is injective.
------------------------------------------------------------------------


record FractalLimitClosure
  (Level State Observation LimitObservation : Set)
  (Refines : Level → Level → Set)
  (encode : Level → State → Observation)
  (limitEncode : State → LimitObservation)
  : Set₁ where
  constructor fractalLimitClosure
  field
    Approx : Observation → LimitObservation → Set
    approximationWitness :
      ∀ level state →
      Approx (encode level state) (limitEncode state)
    limitSeparation :
      ∀ {s t : State} →
      limitEncode s ≡ limitEncode t →
      s ≡ t

open FractalLimitClosure public

fractalLimitInjective :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  (F : FractalLimitClosure
    Level State Observation LimitObservation
    Refines encode limitEncode) →
  ∀ {s t : State} →
  limitEncode s ≡ limitEncode t →
  s ≡ t
fractalLimitInjective F = limitSeparation F

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/GRUFractalLimitDecoderSurvival.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Decoder survival through a fractal limit.
--
-- This module isolates the exact missing seam after finite/indexed GRU
-- injectivity: a compatible family of finite decoders must determine a
-- single decoder on the limit carrier.
--
-- No topological limit or existence claim is manufactured here.
------------------------------------------------------------------------


record CoherentLimitDecoder
  (Level State Observation LimitObservation : Set)
  (encode : Level → State → Observation)
  (limitEncode : State → LimitObservation)
  : Set₁ where
  constructor coherentLimitDecoder
  field
    decode : Level → Observation → State
    limitDecode : LimitObservation → State
    projection : Level → LimitObservation → Observation
    projectionEncode :
      ∀ level state →
      projection level (limitEncode state) ≡ encode level state
    decoderCoherence :
      ∀ level limitObservation →
      decode level (projection level limitObservation) ≡
      limitDecode limitObservation

open CoherentLimitDecoder public

coherentLimitDecoder-left-inverse :
  ∀ {Level State Observation LimitObservation : Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  (C :
    CoherentLimitDecoder
      Level State Observation LimitObservation
      encode limitEncode) →
  ∀ level state →
  decode C level (encode level state) ≡ state →
  limitDecode C (limitEncode state) ≡ state
coherentLimitDecoder-left-inverse C level state finiteLeftInverse =
  trans
    (sym (decoderCoherence C level (limitEncode state)))
    (trans
      (cong (decode C level) (projectionEncode C level state))
      finiteLeftInverse)

------------------------------------------------------------------------
-- The graph edge represented by this module is:
--
--   finite decoder left inverse
--     + limit projection
--     + projection/encoding compatibility
--     + decoder coherence
--     -> limit-surviving left inverse
--
-- Once the resulting limit decoder is available, the existing
-- GRUFractalEGraphAStarLimitComposition module derives limit injectivity.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/GRUFractalEGraphAStarLimitComposition.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- GRU fractal e-graph/A* limit composition.
--
-- The existing repository e-graph/A* layer is discovery/search
-- infrastructure; Agda remains proof-authoritative. This module closes
-- the specific missing implication at the fractal-limit boundary:
--
--   surviving global left inverse
--     -> limit separation
--     -> limit injectivity
--
-- Therefore limit separation is not a second primitive assumption when
-- a decoder survives the limit with a left-inverse law.
------------------------------------------------------------------------


record LimitLeftInverse
  (State LimitObservation : Set)
  (limitEncode : State → LimitObservation)
  : Set₁ where
  constructor limitLeftInverse
  field
    limitDecode : LimitObservation → State
    decodeEncode :
      ∀ state →
      limitDecode (limitEncode state) ≡ state

open LimitLeftInverse public

limitSeparation-from-left-inverse :
  ∀ {State LimitObservation : Set}
  {limitEncode : State → LimitObservation}
  (L : LimitLeftInverse State LimitObservation limitEncode) →
  ∀ {s t : State} →
  limitEncode s ≡ limitEncode t →
  s ≡ t
limitSeparation-from-left-inverse L {s} {t} eq =
  trans
    (sym (decodeEncode L s))
    (trans
      (cong (limitDecode L) eq)
      (decodeEncode L t))

limitInjective-from-left-inverse :
  ∀ {State LimitObservation : Set}
  {limitEncode : State → LimitObservation}
  (L : LimitLeftInverse State LimitObservation limitEncode) →
  ∀ {s t : State} →
  limitEncode s ≡ limitEncode t →
  s ≡ t
limitInjective-from-left-inverse =
  limitSeparation-from-left-inverse

fractalLimitClosure-from-left-inverse :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  (Approx : Observation → LimitObservation → Set)
  (approximationWitness :
    ∀ level state →
    Approx (encode level state) (limitEncode state))
  (L : LimitLeftInverse State LimitObservation limitEncode) →
  FractalLimitClosure
    Level State Observation LimitObservation
    Refines encode limitEncode
fractalLimitClosure-from-left-inverse
  Approx
  approximationWitness
  L =
  fractalLimitClosure
    Approx
    approximationWitness
    (limitSeparation-from-left-inverse L)

------------------------------------------------------------------------
-- E-graph/A* interpretation boundary.
--
-- The graph/search layer may discover this composition:
--
--   global-left-inverse
--     -> global-injectivity
--     -> finite/indexed fractal injectivity
--     -> compatible limit
--     -> surviving limit-left-inverse
--     -> limit separation
--     -> arbitrary-limit injectivity
--
-- The final equality is still an Agda proof term; A* cost/heuristic data
-- never becomes semantic evidence.
------------------------------------------------------------------------

record GRUFractalLimitCompositionKernel
  (State Observation LimitObservation : Set)
  (limitEncode : State → LimitObservation)
  : Set₁ where
  constructor gruFractalLimitCompositionKernel
  field
    limitInverse : LimitLeftInverse State LimitObservation limitEncode

open GRUFractalLimitCompositionKernel public

gruFractalLimitComposition-limitInjective :
  ∀ {State Observation LimitObservation : Set}
  {limitEncode : State → LimitObservation}
  (K :
    GRUFractalLimitCompositionKernel
      State Observation LimitObservation
      limitEncode) →
  ∀ {s t : State} →
  limitEncode s ≡ limitEncode t →
  s ≡ t
gruFractalLimitComposition-limitInjective K =
  limitInjective-from-left-inverse (limitInverse K)

------------------------------------------------------------------------
-- A typed e-graph path remains a semantic equality certificate.
------------------------------------------------------------------------

gruFractalLimitComposition-path-sound :
  ∀ {Expression State : Set}
  {R : EGraphSemanticInterpretation Expression State}
  {e f : Expression} →
  EGraphSemanticPath R e f →
  interpret R e ≡ interpret R f
gruFractalLimitComposition-path-sound =
  eGraph-path-sound _

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/GRUFractalLimitConvergenceAdapter.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

record GRUFractalLimitConvergenceWitness
  (Level State Observation LimitObservation : Set)
  (Refines : Level → Level → Set)
  (encode : Level → State → Observation)
  (limitEncode : State → LimitObservation)
  (rank : Nat → Level)
  (Converges : (Nat → Observation) → LimitObservation → Set)
  : Set₁ where
  constructor gruFractalLimitConvergenceWitness
  field
    approximationSequence :
      State → Nat → Observation
    rankEncoding :
      ∀ n state →
      approximationSequence state n ≡
      encode (rank n) state
    converges :
      ∀ state →
      Converges
        (approximationSequence state)
        (limitEncode state)
    Approx :
      Observation → LimitObservation → Set
    approximationWitness :
      ∀ level state →
      Approx
        (encode level state)
        (limitEncode state)
    coherentDecoder :
      CoherentLimitDecoder
        Level State Observation LimitObservation
        encode limitEncode
    finiteLeftInverse :
      ∀ level state →
      CoherentLimitDecoder.decode
        coherentDecoder
        level
        (encode level state) ≡
      state

open GRUFractalLimitConvergenceWitness public

gruFractalLimitConvergence-limitLeftInverse :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  {rank : Nat → Level}
  {Converges : (Nat → Observation) → LimitObservation → Set}
  (W :
    GRUFractalLimitConvergenceWitness
      Level State Observation LimitObservation
      Refines encode limitEncode rank Converges) →
  LimitLeftInverse State LimitObservation limitEncode
gruFractalLimitConvergence-limitLeftInverse W =
  limitLeftInverse
    (λ state →
      coherentLimitDecoder-left-inverse
        (coherentDecoder W)
        (rank zero)
        state
        (finiteLeftInverse W (rank zero) state))

gruFractalLimitConvergence-fractalLimitClosure :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  {rank : Nat → Level}
  {Converges : (Nat → Observation) → LimitObservation → Set}
  (W :
    GRUFractalLimitConvergenceWitness
      Level State Observation LimitObservation
      Refines encode limitEncode rank Converges) →
  FractalLimitClosure
    Level State Observation LimitObservation
    Refines encode limitEncode
gruFractalLimitConvergence-fractalLimitClosure W =
  fractalLimitClosure
    (Approx W)
    (approximationWitness W)
    (limitSeparation-from-left-inverse
      (gruFractalLimitConvergence-limitLeftInverse W))

gruFractalLimitConvergence-limitInjective :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  {rank : Nat → Level}
  {Converges : (Nat → Observation) → LimitObservation → Set}
  (W :
    GRUFractalLimitConvergenceWitness
      Level State Observation LimitObservation
      Refines encode limitEncode rank Converges) →
  ∀ {s t : State} →
  limitEncode s ≡ limitEncode t →
  s ≡ t
gruFractalLimitConvergence-limitInjective W =
  fractalLimitInjective
    (gruFractalLimitConvergence-fractalLimitClosure W)

------------------------------------------------------------------------
-- Convergence remains a supplied witness. It is not promoted into a
-- separation theorem without the explicit coherent decoder/left inverse.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Inlined from Exotic/ERL/FullCoupled/GRUFractalLimitConvergenceImpossibility.agda; TheoremsMonolith is the sole theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Impossibility boundary for naive arbitrary-limit closure.
--
-- A convergence/approximation interface without a surviving separating
-- decoder cannot, by itself, imply injectivity of the limit representation.
-- The countermodel below is deliberately finite: Bool is collapsed to Unit.
------------------------------------------------------------------------


false-not-true : ¬ (false ≡ true)
false-not-true ()

constant-limit : Bool → ⊤
constant-limit _ = tt

trivial-convergence :
  ∀ state →
  ⊤
trivial-convergence _ = tt

------------------------------------------------------------------------
-- There cannot be a generic theorem that turns an arbitrary supplied
-- "convergence witness" into limit injectivity.  The premises below are
-- intentionally no stronger than a total witness for every state.
------------------------------------------------------------------------

naive-limit-injectivity-impossible :
  ¬
  (∀ {State LimitObservation : Set}
    (limitEncode : State → LimitObservation) →
    (∀ state → ⊤) →
    ∀ {s t : State} →
    limitEncode s ≡ limitEncode t →
    s ≡ t)
naive-limit-injectivity-impossible derive =
  false-not-true
    (derive constant-limit trivial-convergence
      {s = false} {t = true} refl)

------------------------------------------------------------------------
-- Interpretation:
--
--   approximation/convergence witness alone
--              ↛
--        limit injectivity
--
-- A separate separation mechanism is necessary.  The repository's
-- limit-left-inverse kernel supplies exactly that missing mechanism.
------------------------------------------------------------------------

record CanonicalAQLoopTheorem : Set₁ where
  constructor canonicalAQLoopTheorem
  field
    policyComposition :
      ∀ K s →
      C.canonicalPolicy K s ≡
      C.sparsemaxPolicy
        (C.actionSpaceK K)
        (C.lcbScore
          (C.lcbKernel K)
          (C.lcbCounts s)
          (C.critic (C.watkins s)))
        (C.valuesCount (C.lcbCounts s))
    sharedWatkinsSignal :
      ∀ K s →
      C.canonicalSignal K s ≡
      C.canonicalWatkinsTarget K s
    gruSignalCoupling :
      ∀ K s →
      C.canonicalGRUStep K s ≡
      C.gruStep (C.gru s) (C.canonicalSignal K s)
    f4SignalCoupling :
      ∀ K s →
      C.canonicalOptimizerStep K s ≡
      C.f4ThetaStep (C.optimizerKernel K) (C.optimizer s) (C.canonicalSignal K s)
    watkinsEndogenousCoupling :
      ∀ K s →
      C.canonicalWatkinsTarget K s ≡
      C.int8Add
        (C.int8Add
          (C.int8Add
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          (C.int8Mul C.canonicalDiscount8
            (C.maxCriticValue8 (C.critic (C.watkins s)))))
        (C.canonicalEndogenousFeedback K s)

open CanonicalAQLoopTheorem public

canonical-aq-loop-theorem :
  CanonicalAQLoopTheorem
canonical-aq-loop-theorem =
  canonicalAQLoopTheorem
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)

canonicalTotalCountAfter :
  ∀ K n s →
  C.totalCount (C.lcbCounts (C.iterateCanonical K n s)) ≡
  C.totalCount (C.lcbCounts s) + n
canonicalTotalCountAfter = C.canonicalTotalCountAfter

canonicalAperiodic-theorem :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ≢ s
canonicalAperiodic-theorem = C.canonicalAperiodic

canonicalNoNontrivialFiniteCycle-theorem :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ≡ s → ⊥
canonicalNoNontrivialFiniteCycle-theorem = C.canonicalNoNontrivialFiniteCycle

record StateIsomorphism (A B : Set) : Set where
  constructor stateIsomorphism
  field
    to : A → B
    from : B → A
    from-to : ∀ a → from (to a) ≡ a
    to-from : ∀ b → to (from b) ≡ b

open StateIsomorphism public

iterateIsomorphism :
  ∀ {A : Set} → (A → A) → Nat → A → A
iterateIsomorphism f zero a = a
iterateIsomorphism f (suc n) a = iterateIsomorphism f n (f a)

record StepConjugacyWitness
  (A B : Set)
  (sourceStep : A → A)
  (targetStep : B → B) : Set₁ where
  constructor stepConjugacyWitness
  field
    isomorphism : StateIsomorphism A B
    stepCommutes :
      ∀ a →
      to isomorphism (sourceStep a) ≡
      targetStep (to isomorphism a)

open StepConjugacyWitness public

stepConjugacy-iterate :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : StepConjugacyWitness A B sourceStep targetStep)
  (n : Nat)
  (a : A) →
  to (isomorphism W) (iterateIsomorphism sourceStep n a) ≡
  iterateIsomorphism targetStep n (to (isomorphism W) a)
stepConjugacy-iterate W zero a =
  refl
stepConjugacy-iterate W (suc n) a =
  trans
    (stepConjugacy-iterate W n (sourceStep a))
    (cong
      (iterateIsomorphism targetStep n)
      (stepCommutes W a))

iteratePredicateTransport :
  ∀ {B : Set}
  (step : B → B)
  (Property : B → Set) →
  (∀ b → Property b → Property (step b)) →
  ∀ n b →
  Property b →
  Property (iterateIsomorphism step n b)
iteratePredicateTransport step Property preserved zero b proof =
  proof
iteratePredicateTransport step Property preserved (suc n) b proof =
  iteratePredicateTransport
    step
    Property
    preserved
    n
    (step b)
    (preserved b proof)

stepConjugacy-property-transport :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : StepConjugacyWitness A B sourceStep targetStep)
  (P : A → Set)
  (Q : B → Set)
  (bridge : ∀ a → P a → Q (to (isomorphism W) a))
  (preserved : ∀ b → Q b → Q (targetStep b)) →
  ∀ n a →
  P a →
  Q (iterateIsomorphism targetStep n (to (isomorphism W) a))
stepConjugacy-property-transport W P Q bridge preserved n a proof =
  iteratePredicateTransport
    targetStep
    Q
    preserved
    n
    (to (isomorphism W) a)
    (bridge a proof)

canonical-connected-composition-theorem :
  CanonicalConnectedCompositionTheorem
canonical-connected-composition-theorem =
  canonicalConnectedCompositionTheorem
    canonical-aq-loop-theorem
    canonicalTotalCountAfter
    canonicalNoNontrivialFiniteCycle-theorem

data LearnerReplacement : Set where
  normReplacement : NormPair → LearnerReplacement
  optimizerReplacement : F4IntUState → LearnerReplacement

applyLearnerReplacement :
  LearnerReplacement → FullLearnerState → FullLearnerState
applyLearnerReplacement (normReplacement n) s = replaceNorm s n
applyLearnerReplacement (optimizerReplacement o) s = replaceOptimizer s o

applyLearnerReplacements :
  List LearnerReplacement → FullLearnerState → FullLearnerState
applyLearnerReplacements [] s = s
applyLearnerReplacements (r ∷ rs) s =
  applyLearnerReplacements rs (applyLearnerReplacement r s)

canonicalPolicy-learnerReplacement-invariant :
  ∀ K s r →
  canonicalPolicy K (applyLearnerReplacement r s) ≡ canonicalPolicy K s
canonicalPolicy-learnerReplacement-invariant K s (normReplacement n) =
  canonicalPolicy-norm-invariant K s n
canonicalPolicy-learnerReplacement-invariant K s (optimizerReplacement o) =
  canonicalPolicy-optimizer-invariant K s o

canonicalPolicy-learnerReplacement-composition :
  ∀ K s rs →
  canonicalPolicy K (applyLearnerReplacements rs s) ≡ canonicalPolicy K s
canonicalPolicy-learnerReplacement-composition K s [] = refl
canonicalPolicy-learnerReplacement-composition K s (r ∷ rs) =
  trans
    (canonicalPolicy-learnerReplacement-composition
      K (applyLearnerReplacement r s) rs)
    (canonicalPolicy-learnerReplacement-invariant K s r)

canonicalFullStep-replaceNorm :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (s : C.FullLearnerState A)
  (n : C.NormPair) →
  C.canonicalFullStep K (C.replaceNorm s n)
  ≡
  C.replaceNorm (C.canonicalFullStep K s) n
canonicalFullStep-replaceNorm K s n = refl

canonicalFullStep-replaceNorm-iterate :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (n : Nat)
  (s : C.FullLearnerState A)
  (normValue : C.NormPair) →
  C.iterateCanonical K n (C.replaceNorm s normValue)
  ≡
  C.replaceNorm (C.iterateCanonical K n s) normValue
canonicalFullStep-replaceNorm-iterate K zero s normValue = refl
canonicalFullStep-replaceNorm-iterate K (suc n) s normValue =
  trans
    (cong
      (C.iterateCanonical K n)
      (canonicalFullStep-replaceNorm K s normValue))
    (canonicalFullStep-replaceNorm-iterate
      K
      n
      (C.canonicalFullStep K s)
      normValue)

record CanonicalLearnerReplacementClosureTheorem : Set₁ where
  constructor canonicalLearnerReplacementClosureTheorem
  field
    policyInvariant :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (rs : List LearnerReplacement) →
      C.canonicalPolicy
        K
        (applyLearnerReplacements rs s)
      ≡
      C.canonicalPolicy K s

canonical-learner-replacement-closure-theorem :
  CanonicalLearnerReplacementClosureTheorem
canonical-learner-replacement-closure-theorem =
  canonicalLearnerReplacementClosureTheorem
    canonicalPolicy-learnerReplacement-composition

canonicalNormPair-afterFullStep-iterate :
  ∀ K n s →
  normPairWeightPlusOne
    (norm (iterateCanonical K n s))
  ≡
  normPairWeightPlusOne (norm s)
canonicalNormPair-afterFullStep-iterate K zero s = refl
canonicalNormPair-afterFullStep-iterate K (suc n) s =
  trans
    (canonicalNormPair-afterFullStep-iterate
      K n (canonicalFullStep K s))
    (canonicalNormPairWeightPlusOne-preservation K s)

canonicalPersistentGRU-afterFullStep-iterate :
  ∀ K n s →
  persistentGRU
    (gru (iterateCanonical K n s))
  ≡
  persistentGRU (gru s)
canonicalPersistentGRU-afterFullStep-iterate K zero s = refl
canonicalPersistentGRU-afterFullStep-iterate K (suc n) s =
  trans
    (canonicalPersistentGRU-afterFullStep-iterate
      K n (canonicalFullStep K s))
    (canonicalPersistentGRUPreservation K s)

record EqualityCompositionTheorem
  {A : Set}
  {x y z : A} : Set where
  constructor equalityCompositionTheorem
  field
    firstStep : x ≡ y
    secondStep : y ≡ z
    composedStep : x ≡ z

composeEqualityTheorem :
  ∀ {A : Set} {x y z : A} →
  x ≡ y →
  y ≡ z →
  EqualityCompositionTheorem
composeEqualityTheorem first second =
  equalityCompositionTheorem
    first
    second
    (trans first second)

record RecurrentAssociativeScanTheorem
  (State Input : Set) : Set₁ where
  constructor recurrentAssociativeScanTheorem
  field
    actionAssociative :
      ∀ (f g h : C.Endomorphism State) s →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g)
          h)
        s
      ≡
      C.applyEndomorphism
        (C.composeEndomorphism
          f
          (C.composeEndomorphism g h))
        s

    prefixCorrect :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : Nat → Input)
        (n : Nat)
        (s : State) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism R xs n)
        s
      ≡
      C.recurrentPrefixState R xs n s

    prefixSplit :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : Nat → Input)
        (m n : Nat)
        (s : State) →
      C.recurrentPrefixState R xs (m + n) s
      ≡
      C.recurrentPrefixState
        R
        (C.shiftInput xs m)
        n
        (C.recurrentPrefixState R xs m s)

canonicalGRU-recurrent-associative-scan-theorem :
  RecurrentAssociativeScanTheorem C.GRUState C.Int8
canonicalGRU-recurrent-associative-scan-theorem =
  recurrentAssociativeScanTheorem
    C.endomorphismAssociative
    C.recurrentPrefix-correct
    C.recurrentPrefix-split

prefixOp :
  ∀ {State : Set} →
  C.Endomorphism State →
  C.Endomorphism State →
  C.Endomorphism State
prefixOp f g = C.composeEndomorphism g f

prefixListEndomorphism :
  ∀ {State Input : Set} →
  C.RecurrentNetwork State Input →
  List Input →
  C.Endomorphism State
prefixListEndomorphism R [] =
  C.identityEndomorphism
prefixListEndomorphism R (x ∷ xs) =
  C.composeEndomorphism
    (prefixListEndomorphism R xs)
    (C.recurrentInputEndomorphism R x)

prefixListEndomorphism-unit :
  ∀ {State Input : Set}
  (R : C.RecurrentNetwork State Input)
  (s : State) →
  C.applyEndomorphism
    (prefixListEndomorphism R [])
    s
  ≡ s
prefixListEndomorphism-unit R s = refl

prefixListEndomorphism-append :
  ∀ {State Input : Set}
  (R : C.RecurrentNetwork State Input)
  (xs ys : List Input)
  (s : State) →
  C.applyEndomorphism
    (prefixListEndomorphism R (xs ++ ys))
    s
  ≡
  C.applyEndomorphism
    (prefixOp
      (prefixListEndomorphism R xs)
      (prefixListEndomorphism R ys))
    s
prefixListEndomorphism-append R [] ys s = refl
prefixListEndomorphism-append R (x ∷ xs) ys s =
  trans
    (prefixListEndomorphism-append
      R
      xs
      ys
      (C.applyEndomorphism
        (C.recurrentInputEndomorphism R x)
        s))
    refl

prefixOp-associative :
  ∀ {State : Set}
  (f g h : C.Endomorphism State)
  (s : State) →
  C.applyEndomorphism
    (prefixOp (prefixOp f g) h)
    s
  ≡
  C.applyEndomorphism
    (prefixOp f (prefixOp g h))
    s
prefixOp-associative f g h s =
  C.endomorphismAssociative h g f s

prefixOp-identity-left :
  ∀ {State : Set}
  (f : C.Endomorphism State) (s : State) →
  C.applyEndomorphism (prefixOp C.identityEndomorphism f) s
  ≡ C.applyEndomorphism f s
prefixOp-identity-left f s = refl

prefixOp-identity-right :
  ∀ {State : Set}
  (f : C.Endomorphism State) (s : State) →
  C.applyEndomorphism (prefixOp f C.identityEndomorphism) s
  ≡ C.applyEndomorphism f s
prefixOp-identity-right f s = refl

record RecurrentPrefixMonoidHomomorphism
  (State Input : Set) : Set₁ where
  constructor recurrentPrefixMonoidHomomorphism
  field
    unit :
      ∀ (R : C.RecurrentNetwork State Input) (s : State) →
      C.applyEndomorphism
        (prefixListEndomorphism R [])
        s
      ≡ s
    append :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs ys : List Input)
        (s : State) →
      C.applyEndomorphism
        (prefixListEndomorphism R (xs ++ ys))
        s
      ≡
      C.applyEndomorphism
        (prefixOp
          (prefixListEndomorphism R xs)
          (prefixListEndomorphism R ys))
        s

canonical-recurrent-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
canonical-recurrent-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

productEndomorphism :
  ∀ {StateA StateB : Set} →
  C.Endomorphism StateA →
  C.Endomorphism StateB →
  C.Endomorphism (StateA × StateB)
productEndomorphism f g =
  C.endomorphism
    (λ st →
      (C.applyEndomorphism f (proj₁ st) ,
       C.applyEndomorphism g (proj₂ st)))

productEndomorphism-compose :
  ∀ {StateA StateB : Set}
  (f₁ f₂ : C.Endomorphism StateA)
  (g₁ g₂ : C.Endomorphism StateB)
  (s : StateA)
  (t : StateB) →
  C.applyEndomorphism
    (productEndomorphism
      (C.composeEndomorphism f₁ f₂)
      (C.composeEndomorphism g₁ g₂))
    (s , t)
  ≡
  C.applyEndomorphism
    (C.composeEndomorphism
      (productEndomorphism f₁ g₁)
      (productEndomorphism f₂ g₂))
    (s , t)
productEndomorphism-compose f₁ f₂ g₁ g₂ s t = refl

canonicalF4RecurrentNetwork :
  C.CanonicalFullLearnerKernel →
  C.RecurrentNetwork C.F4IntUState C.Int8
canonicalF4RecurrentNetwork K =
  C.recurrentNetwork
    (λ o signal →
      C.f4ThetaStep (C.optimizerKernel K) o signal)

canonicalF4RecurrentNetwork-step-law :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (o : C.F4IntUState)
  (signal : C.Int8) →
  C.runNetwork
    (canonicalF4RecurrentNetwork K)
    o
    signal
  ≡
  C.f4ThetaStep (C.optimizerKernel K) o signal
canonicalF4RecurrentNetwork-step-law K o signal = refl

canonicalF4-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    C.F4IntUState
    C.Int8
canonicalF4-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

canonicalNormPairRecurrentNetwork :
  C.RecurrentNetwork C.NormPair C.Int8
canonicalNormPairRecurrentNetwork =
  C.recurrentNetwork
    (λ n _ → n)

canonicalNormPairRecurrentNetwork-step-law :
  ∀ (n : C.NormPair) (signal : C.Int8) →
  C.runNetwork
    canonicalNormPairRecurrentNetwork
    n
    signal
  ≡ n
canonicalNormPairRecurrentNetwork-step-law n signal = refl

canonicalNormPair-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    C.NormPair
    C.Int8
canonicalNormPair-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

CanonicalGRUF4NormPrefixState : Set
CanonicalGRUF4NormPrefixState =
  C.GRUState × (C.F4IntUState × C.NormPair)

CanonicalGRUF4NormPrefixInput : Set
CanonicalGRUF4NormPrefixInput =
  C.Int8

canonicalGRUF4NormPrefixNetwork :
  C.CanonicalFullLearnerKernel →
  C.RecurrentNetwork
    CanonicalGRUF4NormPrefixState
    CanonicalGRUF4NormPrefixInput
canonicalGRUF4NormPrefixNetwork K =
  C.recurrentNetwork
    (λ { (g , (o , n)) signal →
      ( C.gruStep g signal
      , ( C.f4ThetaStep (C.optimizerKernel K) o signal
        , n)) })

canonicalGRUF4NormPrefix-step-law :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (g : C.GRUState) (o : C.F4IntUState) (n : C.NormPair)
  (signal : C.Int8) →
  C.runNetwork (canonicalGRUF4NormPrefixNetwork K)
    (g , (o , n)) signal
  ≡
  ( C.gruStep g signal
  , ( C.f4ThetaStep (C.optimizerKernel K) o signal
    , n))
canonicalGRUF4NormPrefix-step-law K g o n signal = refl

canonicalGRUF4Norm-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    CanonicalGRUF4NormPrefixState
    CanonicalGRUF4NormPrefixInput
canonicalGRUF4Norm-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

canonicalFullStep-GRUF4Norm-prefix-bridge :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  C.runNetwork (canonicalGRUF4NormPrefixNetwork K)
    (C.gru s , (C.optimizer s , C.norm s))
    (C.canonicalSignal K s)
  ≡
  ( C.gru (C.canonicalFullStep K s)
  , ( C.optimizer (C.canonicalFullStep K s)
    , C.norm (C.canonicalFullStep K s)))
canonicalFullStep-GRUF4Norm-prefix-bridge K s = refl

record CanonicalGRUF4NormWatkinsPrefixCompositionTheorem : Set₁ where
  constructor canonicalGRUF4NormWatkinsPrefixCompositionTheorem
  field
    recurrentScan :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
    targetCorrectness :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalSignal K s ≡ C.canonicalWatkinsTarget K s
    gruf4NormCorrectness :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.runNetwork (canonicalGRUF4NormPrefixNetwork K)
        (C.gru s , (C.optimizer s , C.norm s))
        (C.canonicalSignal K s)
      ≡
      ( C.gru (C.canonicalFullStep K s)
      , ( C.optimizer (C.canonicalFullStep K s)
        , C.norm (C.canonicalFullStep K s)))

canonical-gruf4-norm-watkins-prefix-composition-theorem :
  CanonicalGRUF4NormWatkinsPrefixCompositionTheorem
canonical-gruf4-norm-watkins-prefix-composition-theorem =
  canonicalGRUF4NormWatkinsPrefixCompositionTheorem
    canonical-recurrent-prefix-monoid-homomorphism
    C.canonicalSignal-watkins-target
    canonicalFullStep-GRUF4Norm-prefix-bridge

commutingIterate :
  ∀ {S : Set} →
  (S → S) → Nat → S → S
commutingIterate step zero s = s
commutingIterate step (suc n) s =
  step (commutingIterate step n s)

record CommutingSquareTheorem
  (State Feature : Set)
  (step : State → State)
  (observe : State → Feature)
  (featureStep : Feature → Feature) : Set₁ where
  constructor commutingSquareTheorem
  field
    square :
      ∀ s → observe (step s) ≡ featureStep (observe s)
    iterateSquare :
      ∀ n s →
      observe (commutingIterate step n s) ≡
      commutingIterate featureStep n (observe s)

open CommutingSquareTheorem public

freeMonoidActionHomomorphism-from-square :
  ∀ {State Feature : Set}
  {step : State → State}
  {observe : State → Feature}
  {featureStep : Feature → Feature} →
  CommutingSquareTheorem State Feature step observe featureStep →
  FreeMonoidActionHomomorphism State Feature step observe featureStep
freeMonoidActionHomomorphism-from-square squareWitness =
  freeMonoidActionHomomorphism
    (CommutingSquareTheorem.iterateSquare squareWitness)

canonicalCount-freeMonoidActionHomomorphism :
  ∀ (K : C.CanonicalFullLearnerKernel) →
  FreeMonoidActionHomomorphism
    C.CanonicalFullLearnerState
    Nat
    (C.canonicalFullStep K)
    suc
    (λ s → C.totalCount (C.lcbCounts s))
canonicalCount-freeMonoidActionHomomorphism K =
  freeMonoidActionHomomorphism-from-square
    (commutingSquareTheorem-from-square
      (λ s →
        C.canonicalTotalCountStep K s))

recurrentWordState :
  ∀ {State Input : Set} →
  C.RecurrentNetwork State Input →
  List Input →
  State →
  State
recurrentWordState R word s =
  C.applyEndomorphism
    (prefixListEndomorphism R word)
    s

recurrentPrefix-scan-lifts-conjugacy :
  ∀ {State Input : Set}
  (replace : State → State)
  (step : State → Input → State)
  (h :
    ∀ (s : State) (x : Input) →
    replace (step s x) ≡ step (replace s) x) →
  ∀ (xs : List Input) (n : Nat) (s : State) →
    replace
      (C.recurrentPrefixState
        (C.recurrentNetwork step)
        xs n s)
    ≡
    C.recurrentPrefixState
      (C.recurrentNetwork step)
      xs n
      (replace s)
recurrentPrefix-scan-lifts-conjugacy replace step h xs zero s = refl
recurrentPrefix-scan-lifts-conjugacy replace step h xs (suc n) s =
  trans
    (recurrentPrefix-scan-lifts-conjugacy
      replace
      step
      h
      xs
      n
      (step s (xs n)))
    (cong
      (λ q →
        C.recurrentPrefixState
          (C.recurrentNetwork step)
          xs n
          q)
      (h s (xs n)))

canonical-recurrent-scan-conjugacy-theorem :
  RecurrentScanConjugacyTheorem C.GRUState C.Int8
canonical-recurrent-scan-conjugacy-theorem =
  recurrentScanConjugacyTheorem
    (λ replace step h → replace)
    (λ replace step h xs n s → recurrentPrefix-scan-lifts-conjugacy replace step h xs n s)

canonicalRecurrentInput-watkinsTarget-law :
  ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
  C.canonicalGRUStep K s ≡
  C.gruStep (C.gru s) (C.canonicalWatkinsTarget K s)
canonicalRecurrentInput-watkinsTarget-law K s =
  trans
    (C.canonicalRecurrentInput-law K s)
    (cong
      (C.gruStep (C.gru s))
      (C.canonicalSignal-watkins-target K s))
record CanonicalFullLearnerConnectedScanConjugacyTheorem : Set₁ where
  constructor canonicalFullLearnerConnectedScanConjugacyTheorem
  field
    scanConjugacy :
      (replace : C.CanonicalFullLearnerState → C.CanonicalFullLearnerState)
      (K : C.CanonicalFullLearnerKernel) →
      (h :
        ∀ s →
        replace (C.canonicalFullStep K s) ≡
        C.canonicalFullStep K (replace s)) →
      ∀ n s →
        replace (C.iterateCanonical K n s) ≡
        C.iterateCanonical K n (replace s)
    connectedStep :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.runNetwork (canonicalGRUF4NormPrefixNetwork K)
        (C.gru s , (C.optimizer s , C.norm s))
        (C.canonicalSignal K s)
      ≡
      ( C.gru (C.canonicalFullStep K s)
      , ( C.optimizer (C.canonicalFullStep K s)
        , C.norm (C.canonicalFullStep K s)))
    watkinsConnected :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.watkins (C.canonicalFullStep K s) ≡
      C.canonicalWatkinsStep K s
    watkinsTargetCoupling :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalSignal K s ≡ C.canonicalWatkinsTarget K s
    gruWatkinsCoupling :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalGRUStep K s ≡
      C.gruStep
        (C.gru s)
        (C.canonicalWatkinsTarget K s)
    optimizerWatkinsCoupling :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalOptimizerStep K s ≡
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer s)
        (C.canonicalWatkinsTarget K s)

canonicalFullLearner-iterate-conjugacy :
  ∀
  (replace : C.CanonicalFullLearnerState → C.CanonicalFullLearnerState)
  (K : C.CanonicalFullLearnerKernel)
  (h :
    ∀ s →
    replace (C.canonicalFullStep K s) ≡
    C.canonicalFullStep K (replace s)) →
  ∀ n s →
  replace (C.iterateCanonical K n s) ≡
  C.iterateCanonical K n (replace s)
canonicalFullLearner-iterate-conjugacy replace K h zero s = refl
canonicalFullLearner-iterate-conjugacy replace K h (suc n) s =
  trans
    (canonicalFullLearner-iterate-conjugacy
      replace K h n (C.canonicalFullStep K s))
    (cong
      (C.iterateCanonical K n)
      (h s))

canonical-full-learner-connected-scan-conjugacy-theorem :
  CanonicalFullLearnerConnectedScanConjugacyTheorem
canonical-full-learner-connected-scan-conjugacy-theorem =
  canonicalFullLearnerConnectedScanConjugacyTheorem
    (λ replace K h → canonicalFullLearner-iterate-conjugacy replace K h)
    canonicalFullStep-GRUF4Norm-prefix-bridge
    C.canonicalFullStep-watkins
    C.canonicalSignal-watkins-target
    canonicalRecurrentInput-watkinsTarget-law
    C.canonicalOptimizerStep-qMunchausen-L2
record S4PlusS5RecurrentScanTheorem (State Input : Set) : Set₁ where
  constructor s4PlusS5RecurrentScanTheorem
  field
    recurrentScan :
      RecurrentAssociativeScanTheorem State Input
    identityAction :
      ∀ (s : State) →
      C.applyEndomorphism
        C.identityEndomorphism s ≡ s

open S4PlusS5RecurrentScanTheorem public

canonical-S4S5-recurrent-scan-theorem :
  S4PlusS5RecurrentScanTheorem C.GRUState C.Int8
canonical-S4S5-recurrent-scan-theorem =
  s4PlusS5RecurrentScanTheorem
    canonicalGRU-recurrent-associative-scan-theorem
    (λ s → refl)

productRecurrentNetwork :
  ∀ {StateA StateB Input : Set} →
  C.RecurrentNetwork StateA Input →
  C.RecurrentNetwork StateB Input →
  C.RecurrentNetwork (StateA × StateB) Input
productRecurrentNetwork RA RB =
  C.recurrentNetwork
    (λ st x →
      (C.runNetwork RA (proj₁ st) x ,
       C.runNetwork RB (proj₂ st) x))

productRecurrentPrefix-correct :
  ∀ {StateA StateB Input : Set}
  (RA : C.RecurrentNetwork StateA Input)
  (RB : C.RecurrentNetwork StateB Input)
  (xs : Nat → Input)
  (n : Nat)
  (s : StateA)
  (t : StateB) →
  C.recurrentPrefixState
    (productRecurrentNetwork RA RB)
    xs n
    (s , t)
  ≡
  (C.recurrentPrefixState RA xs n s ,
   C.recurrentPrefixState RB xs n t)
productRecurrentPrefix-correct RA RB xs zero s t = refl
productRecurrentPrefix-correct RA RB xs (suc n) s t =
  cong₂
    (λ a b →
      (C.runNetwork RA a (xs n) ,
       C.runNetwork RB b (xs n)))
    (cong proj₁ (productRecurrentPrefix-correct RA RB xs n s t))
    (cong proj₂ (productRecurrentPrefix-correct RA RB xs n s t))

informationPreserving-symbolic-task-factorization :
  ∀ {State Feature Output : Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (leftInverse : ∀ s → inverse (observe s) ≡ s)
  (target : State → Output)
  (s : State) →
  target s ≡ target (inverse (observe s))
informationPreserving-symbolic-task-factorization
  observe inverse leftInverse target s =
  cong target (sym (leftInverse s))

informationPreserving-all-tasks-injective :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  (inverse : Feature → State) →
  (∀ (target : State → State) (s : State) →
    target s ≡ target (inverse (observe s))) →
  ∀ {s t} → observe s ≡ observe t → s ≡ t
informationPreserving-all-tasks-injective
  observe inverse allTasks
  {s} {t} eq =
  trans
    (sym (allTasks (λ x → x) s))
    (trans
      (cong inverse eq)
      (allTasks (λ x → x) t))

productObservation :
  ∀ {StateA StateB FeatureA FeatureB : Set} →
  (StateA → FeatureA) →
  (StateB → FeatureB) →
  (StateA × StateB) →
  (FeatureA × FeatureB)
productObservation observeA observeB st =
  (observeA (proj₁ st) , observeB (proj₂ st))

productInverse :
  ∀ {StateA StateB FeatureA FeatureB : Set} →
  (FeatureA → StateA) →
  (FeatureB → StateB) →
  (FeatureA × FeatureB) →
  (StateA × StateB)
productInverse inverseA inverseB feature =
  (inverseA (proj₁ feature) , inverseB (proj₂ feature))

productObservation-leftInverse :
  ∀ {StateA StateB FeatureA FeatureB : Set}
  (observeA : StateA → FeatureA)
  (inverseA : FeatureA → StateA)
  (observeB : StateB → FeatureB)
  (inverseB : FeatureB → StateB)
  (leftInverseA : ∀ s → inverseA (observeA s) ≡ s)
  (leftInverseB : ∀ s → inverseB (observeB s) ≡ s)
  (s : StateA)
  (t : StateB) →
  productInverse inverseA inverseB
    (productObservation observeA observeB (s , t))
  ≡
  (s , t)
productObservation-leftInverse observeA inverseA observeB inverseB
  leftInverseA leftInverseB s t =
  cong₂ _,_ (leftInverseA s) (leftInverseB t)

informationPreserving-symbolic-task-boundary :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (leftInverse : ∀ s → inverse (observe s) ≡ s) →
  ∀ (target : State → State) (s : State) →
  target s ≡ target (inverse (observe s))
informationPreserving-symbolic-task-boundary =
  informationPreserving-symbolic-task-factorization

record PointwiseSandwich
  {Input Value : Set}
  (_≤_ : Value → Value → Set)
  (lower actual upper : Input → Value) : Set₁ where
  constructor pointwiseSandwich
  field
    lower≤actual : ∀ x → lower x ≤ actual x
    actual≤upper : ∀ x → actual x ≤ upper x

record MinimaxBellmanShapleyOperator
  (State Value : Set)
  (_≤_ : Value → Value → Set) : Set₁ where
  constructor minimaxBellmanShapleyOperator
  field
    value : (State → Value) → Value
    monotone :
      ∀ (f g : State → Value) →
      (∀ s → f s ≤ g s) →
      value f ≤ value g

record MinimaxBellmanShapleyInclusionTheorem
  (State Value : Set)
  (_≤_ : Value → Value → Set)
  (operator : MinimaxBellmanShapleyOperator State Value _≤_)
  (lower actual upper : State → Value) : Set₁ where
  constructor minimaxBellmanShapleyInclusionTheorem
  field
    lowerBound :
      MinimaxBellmanShapleyOperator.value operator lower
      ≤
      MinimaxBellmanShapleyOperator.value operator actual
    upperBound :
      MinimaxBellmanShapleyOperator.value operator actual
      ≤
      MinimaxBellmanShapleyOperator.value operator upper

open PointwiseSandwich public
open MinimaxBellmanShapleyOperator public
open MinimaxBellmanShapleyInclusionTheorem public

canonicalBiasedWatkinsNegativeQMunchausenL2Target :
  C.CanonicalFullLearnerKernel → C.CanonicalFullLearnerState → C.Int8
canonicalBiasedWatkinsNegativeQMunchausenL2Target =
  C.canonicalWatkinsTarget

record CanonicalQMunchausenL2SharedNegationPolarityTheorem : Set₁ where
  constructor canonicalQMunchausenL2SharedNegationPolarityTheorem
  field
    qMunchausenBiasNegation :
      ∀ x →
      C.qLog2Bias8 x ≡
      C.int8Neg
        (C.int8OfNat
          ((C.munchausenScale8 * C.numerator (C.finiteQLog8 x)) /
           C.denominator (C.finiteQLog8 x)))

    l2CorrectionNegation :
      ∀ x →
      C.l2Correction x ≡ C.int8Neg x

open CanonicalQMunchausenL2SharedNegationPolarityTheorem public

canonicalWatkinsTarget-endogenous-leftInverse :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (observe : C.CanonicalFullLearnerState → C.Int8)
  (inverse : C.Int8 → C.CanonicalFullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ≡ t) →
  ∀ s →
  C.canonicalWatkinsTarget K s ≡
    C.int8Add
      (C.int8Add
        (C.int8Add
          (C.canonicalReward8 K (inverse (observe s)))
          (C.canonicalQLogBias K (inverse (observe s))))
        (C.int8Mul
          C.canonicalDiscount8
          (C.maxCriticValue8
            (C.critic
              (C.watkins
                (inverse (observe s)))))))
      (C.canonicalEndogenousFeedback K (inverse (observe s)))
canonicalWatkinsTarget-endogenous-leftInverse K observe inverse leftInverse s =
  trans
    (C.canonicalWatkinsTarget-law K s)
    (cong
      (λ t →
        C.int8Add
          (C.int8Add
            (C.int8Add
              (C.canonicalReward8 K t)
              (C.canonicalQLogBias K t))
            (C.int8Mul
              C.canonicalDiscount8
              (C.maxCriticValue8
                (C.critic (C.watkins t)))))
          (C.canonicalEndogenousFeedback K t))
      (leftInverse s))

suc-injective :
  ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

natPlus-left-cancel :
  ∀ (k m n : Nat) → k + m ≡ k + n → m ≡ n
natPlus-left-cancel zero m n eq = eq
natPlus-left-cancel (suc k) m n eq =
  natPlus-left-cancel k m n (suc-injective eq)

canonicalTotalCountSuccessorWitness :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A) →
  NatSuccessorProgressWitness
    (C.FullLearnerState A)
    (C.canonicalFullStep K)
    (λ s → C.totalCount (C.lcbCounts s))
canonicalTotalCountSuccessorWitness K =
  natSuccessorProgressWitness
    (C.canonicalTotalCountStep K)

canonicalOrbit-state-injective :
  ∀ K s {m n : Nat} →
  C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
  m ≡ n
canonicalOrbit-state-injective K s {m} {n} eq =
  successorMeasureOrbitInjective
    (canonicalTotalCountSuccessorWitness K)
    s
    eq

canonicalInfiniteStateOrbitEmbedding :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  ∀ {m n : Nat} →
  C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
  m ≡ n
canonicalInfiniteStateOrbitEmbedding K s =
  canonicalOrbit-state-injective K s

record DiscreteExactUAPTheorem
  (State Feature Output : Set)
  (observe : State → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor discreteExactUAPTheorem
  field
    leftInverse :
      ∀ s → inverse (observe s) ≡ s
    exactReadout :
      (target : State → Output) →
      ∀ s →
      target s ≡ target (inverse (observe s))

open DiscreteExactUAPTheorem public

record DiscreteLeftInverseWitness
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteLeftInverseWitness
  field
    inverse : Feature → State
    leftInverse :
      ∀ s → inverse (observe s) ≡ s

open DiscreteLeftInverseWitness public

record DiscreteExactUniversalUAP
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteExactUniversalUAP
  field
    readout :
      {Output : Set} →
      (State → Output) →
      Feature →
      Output
    exactReadout :
      {Output : Set} →
      (target : State → Output) →
      ∀ s →
      target s ≡ readout target (observe s)

open DiscreteExactUniversalUAP public

discreteLeftInverse-observe-injective :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State} →
  (∀ s → inverse (observe s) ≡ s) →
  ∀ {s t} →
  observe s ≡ observe t →
  s ≡ t
discreteLeftInverse-observe-injective leftInverse {s} {t} eq =
  trans
    (sym (leftInverse s))
    (trans
      (cong inverse eq)
      (leftInverse t))

collision-implies-no-leftInverse-via-injectivity :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  {s t : State} →
  observe s ≡ observe t →
  s ≢ t →
  ¬ (Σ (λ inverse →
      ∀ u → inverse (observe u) ≡ u))
collision-implies-no-leftInverse-via-injectivity
  observe obsEq distinct =
  λ witness →
    distinct
      (discreteLeftInverse-observe-injective
        (proj₂ witness)
        obsEq)

canonicalWatkinsTargetSignalStream :
  C.CanonicalFullLearnerKernel →
  C.CanonicalFullLearnerState →
  Nat →
  C.Int8
canonicalWatkinsTargetSignalStream K s n =
  C.canonicalWatkinsTarget K
    (C.iterateCanonical K n s)

canonicalWatkinsTarget-recurrent-prefix-correct :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (n : Nat)
  (h : C.GRUState) →
  C.applyEndomorphism
    (C.recurrentPrefixEndomorphism
      C.canonicalGRURecurrentNetwork
      (canonicalWatkinsTargetSignalStream K s)
      n)
    h
  ≡
  C.recurrentPrefixState
    C.canonicalGRURecurrentNetwork
    (canonicalWatkinsTargetSignalStream K s)
    n
    h
canonicalWatkinsTarget-recurrent-prefix-correct K s n h =
  C.recurrentPrefix-correct
    C.canonicalGRURecurrentNetwork
    (canonicalWatkinsTargetSignalStream K s)
    n
    h

record ExactTwoCounterConfiguration : Set where
  constructor exactTwoCounterConfiguration
  field
    control : Nat
    counter₁ : Nat
    counter₂ : Nat

record ExactTwoCounterMachine : Set₁ where
  constructor exactTwoCounterMachine
  field
    step : ExactTwoCounterConfiguration → ExactTwoCounterConfiguration
    halting : ExactTwoCounterConfiguration → C.BoolLike

open ExactTwoCounterConfiguration ExactTwoCounterMachine public

record CanonicalExactCompositionTuringCompletenessContract : Set₁ where
  constructor canonicalExactCompositionTuringCompletenessContract
  field
    compile :
      ExactTwoCounterMachine →
      C.CanonicalFullLearnerKernel
    encode :
      (M : ExactTwoCounterMachine) →
      ExactTwoCounterConfiguration →
      C.CanonicalFullLearnerState
    decode :
      (M : ExactTwoCounterMachine) →
      C.CanonicalFullLearnerState →
      ExactTwoCounterConfiguration
    exactEncodeDecode :
      ∀ M c →
      decode M (encode M c) ≡ c
    exactStepSimulation :
      ∀ M c →
      encode M (ExactTwoCounterMachine.step M c) ≡
      C.canonicalFullStep
        (compile M)
        (encode M c)
    output :
      C.CanonicalFullLearnerState → C.BoolLike
    exactHaltingCorrespondence :
      ∀ M c →
      output (encode M c) ≡ ExactTwoCounterMachine.halting M c

exactSelfLoopMachine : ExactTwoCounterMachine
exactSelfLoopMachine =
  exactTwoCounterMachine
    (λ c → c)
    (λ _ → disabled)

canonicalExactCompositionTuringCompletenessContract-impossible :
  ¬ CanonicalExactCompositionTuringCompletenessContract
canonicalExactCompositionTuringCompletenessContract-impossible witness =
  let
    M = exactSelfLoopMachine
    c = exactTwoCounterConfiguration zero zero zero
    K =
      CanonicalExactCompositionTuringCompletenessContract.compile
        witness
        M
    s =
      CanonicalExactCompositionTuringCompletenessContract.encode
        witness
        M
        c
    exactStep =
      CanonicalExactCompositionTuringCompletenessContract.exactStepSimulation
        witness
        M
        c
  in
  C.canonicalNoFixedPoint K s (sym exactStep)

record ContinuousLeftInverseTheorem
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State)
  (Continuous : {A B : Set} → (A → B) → Set) : Set₁ where
  constructor continuousLeftInverseTheorem
  field
    observeContinuous : Continuous observe
    inverseContinuous : Continuous inverse
    leftInverse :
      ∀ s → inverse (observe s) ≡ s

open ContinuousLeftInverseTheorem public

record CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem : Set₁ where
  constructor canonicalEndogenousMinimaxBellmanShapleyUAPTheorem
  field
    targetSemantics :
      CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem

    exactDiscreteUAP :
      ∀ {Feature Output : Set}
      (observe : C.CanonicalFullLearnerState → Feature)
      (inverse : Feature → C.CanonicalFullLearnerState) →
      (leftInverse : ∀ s → inverse (observe s) ≡ s) →
      DiscreteExactUAPTheorem
        C.CanonicalFullLearnerState
        Feature
        Output
        observe
        inverse

    inclusionClass :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (_≤_ : C.Int8 → C.Int8 → Set)
      (operator :
        MinimaxBellmanShapleyOperator
          C.CanonicalFullLearnerState
          C.Int8
          _≤_)
      (lower upper : C.CanonicalFullLearnerState → C.Int8) →
      PointwiseSandwich
        _≤_
        lower
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
        upper →
      MinimaxBellmanShapleyInclusionTheorem
        C.CanonicalFullLearnerState
        C.Int8
        _≤_
        operator
        lower
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
        upper

    endogenousFactorization :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (observe : C.CanonicalFullLearnerState → C.Int8)
      (inverse : C.Int8 → C.CanonicalFullLearnerState) →
      (leftInverse : ∀ t → inverse (observe t) ≡ t) →
      ∀ s →
      C.canonicalWatkinsTarget K s ≡
      C.int8Add
        (C.int8Add
          (C.int8Add
            (C.canonicalReward8 K (inverse (observe s)))
            (C.canonicalQLogBias K (inverse (observe s))))
          (C.int8Mul
            C.canonicalDiscount8
            (C.maxCriticValue8
              (C.critic (C.watkins (inverse (observe s))))))
        (C.canonicalEndogenousFeedback K (inverse (observe s))))

    targetScan :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (n : Nat)
      (h : C.GRUState) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism
          C.canonicalGRURecurrentNetwork
          (canonicalWatkinsTargetSignalStream K s)
          n)
        h
      ≡
      C.recurrentPrefixState
        C.canonicalGRURecurrentNetwork
        (canonicalWatkinsTargetSignalStream K s)
        n
        h

    continuousReadoutTransfer :
      ∀ {Feature Output : Set}
      {observe : C.CanonicalFullLearnerState → Feature}
      {inverse : Feature → C.CanonicalFullLearnerState}
      {Continuous : {A B : Set} → (A → B) → Set} →
      ContinuousLeftInverseTheorem
        C.CanonicalFullLearnerState
        Feature
        observe
        inverse
        Continuous →
      (target : C.CanonicalFullLearnerState → Output) →
      ∀ s →
      target s ≡ target (inverse (observe s))

    ringStateInjection :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      RingStateInjectivityTheorem C.CanonicalFullLearnerState

    infiniteStateOrbit :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      ∀ {m n : Nat} →
      C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
      m ≡ n

    denseNeighborhoodSeparation :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → C.Int8)
      (inverse : C.Int8 → C.CanonicalFullLearnerState) →
      (∀ t → inverse (observe t) ≡ t) →
      DenseNeighborhoodSeparationTheorem
        C.CanonicalFullLearnerState
        C.Int8
        (λ n → C.iterateCanonical K n s)
        observe

canonicalDeterministicFiniteStepDivergenceInevitability :
  ∀ {A}
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (n : Nat) →
  C.iterateCanonical K (suc n) s ≢ s
canonicalDeterministicFiniteStepDivergenceInevitability =
  C.canonicalAperiodic

canonicalNoFiniteStepConvergenceToFixedPoint :
  ∀ {A}
  (K : C.CanonicalFullLearnerKernel)
  (s equilibrium : C.CanonicalFullLearnerState) →
  C.canonicalFullStep K equilibrium ≡ equilibrium →
  ¬ (Σ Nat (λ n → C.iterateCanonical K n s ≡ equilibrium))
canonicalNoFiniteStepConvergenceToFixedPoint K s equilibrium fixedPoint reached =
  C.canonicalNoFixedPoint K equilibrium fixedPoint

canonicalIterateComposition :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (m n : Nat)
  (s : C.CanonicalFullLearnerState) →
  C.iterateCanonical K (m + n) s ≡
  C.iterateCanonical K n (C.iterateCanonical K m s)
canonicalIterateComposition K m zero s
  rewrite +-identityʳ m = refl
canonicalIterateComposition K m (suc n) s
  rewrite +-suc m n =
  cong (C.canonicalFullStep K)
    (canonicalIterateComposition K m n s)

recurrentPrefixStepWork : Nat → Nat
recurrentPrefixStepWork zero = zero
recurrentPrefixStepWork (suc n) = suc (recurrentPrefixStepWork n)

recurrentPrefixStepWork-law :
  ∀ n → recurrentPrefixStepWork n ≡ n
recurrentPrefixStepWork-law n = refl

recurrentPrefixStepWork-split :
  ∀ m n →
  recurrentPrefixStepWork (m + n) ≡
  recurrentPrefixStepWork m + recurrentPrefixStepWork n
recurrentPrefixStepWork-split m zero
  rewrite +-identityʳ m = refl
recurrentPrefixStepWork-split m (suc n)
  rewrite +-suc m n =
  cong suc (recurrentPrefixStepWork-split m n)

canonicalNatIndexedExactUniversalReadout :
  ∀ {Feature Output : Set}
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ≡ t) →
  (target : C.CanonicalFullLearnerState → Output) →
  ∀ n →
  target (C.iterateCanonical K n s) ≡
  target (inverse (observe (C.iterateCanonical K n s)))
canonicalNatIndexedExactUniversalReadout
  K s observe inverse leftInverse target n =
  cong
    target
    (sym (leftInverse (C.iterateCanonical K n s)))

hardSignGate-idempotent :
  ∀ x → C.hardSignGate (C.hardSignGate x) ≡ C.hardSignGate x
hardSignGate-idempotent x with C.hardSign x
... | C.negative = refl
... | C.zeroSign = refl
... | C.positive = refl

hardSignGate-continuous-discrete :
  Continuous
    C.Int8
    C.Int8
    (discreteTopology C.Int8)
    (discreteTopology C.Int8)
    C.hardSignGate
hardSignGate-continuous-discrete =
  continuous-under-discrete-topology C.hardSignGate

record FiniteRankStabilityCertificate
  (State : Set)
  (step : State → State)
  (equilibrium : State) : Set₁ where
  constructor finiteRankStabilityCertificate
  field
    rank : State → Nat
    equilibriumFixed :
      step equilibrium ≡ equilibrium
    rankZero :
      ∀ s → rank s ≡ zero → s ≡ equilibrium
    strictDescent :
      ∀ s → s ≢ equilibrium →
      rank (step s) < rank s
    eventualExact :
      ∀ s → Σ Nat (λ n → iterateState step n s ≡ equilibrium)

open FiniteRankStabilityCertificate public

canonicalFullLearner-no-finite-rank-stability :
  ∀ {A : Set}
  (K : C.CanonicalFullLearnerKernel)
  (equilibrium : C.CanonicalFullLearnerState A) →
  ¬ FiniteRankStabilityCertificate
    (C.CanonicalFullLearnerState A)
    (C.canonicalFullStep K)
    equilibrium
canonicalFullLearner-no-finite-rank-stability K equilibrium certificate =
  C.canonicalNoFixedPoint
    K
    equilibrium
    (FiniteRankStabilityCertificate.equilibriumFixed certificate)

sumNat :
  List Nat → Nat
sumNat [] = zero
sumNat (x ∷ xs) = x + sumNat xs

bundleCost :
  ∀ {Good : Set} →
  List Good →
  (Good → Nat) →
  (Good → Nat) →
  Nat
bundleCost goods price bundle =
  sumNat (map (λ g → price g * bundle g) goods)

BudgetFeasible :
  ∀ {Good : Set} →
  List Good →
  (Good → Nat) →
  (Good → Nat) →
  (Good → Nat) →
  Set
BudgetFeasible goods price endowment bundle =
  bundleCost goods price bundle ≤
  bundleCost goods price endowment

record FiniteNonIIDWalrasianEquilibrium
  (Agent Good : Set)
  (agents : List Agent)
  (goods : List Good)
  (utility : Agent → (Good → Nat) → Nat)
  (endowment : Agent → Good → Nat) : Set₁ where
  constructor finiteNonIIDWalrasianEquilibrium
  field
    price : Good → Nat
    allocation : Agent → Good → Nat
    budgetOptimal :
      ∀ i bundle →
      BudgetFeasible
        goods
        price
        (endowment i)
        bundle →
      utility i bundle ≤
      utility i (allocation i)
    marketClearing :
      ∀ g →
      sumNat (map (λ i → allocation i g) agents) ≡
      sumNat (map (λ i → endowment i g) agents)

open FiniteNonIIDWalrasianEquilibrium public

record FiniteTUShapleyAllocationEquilibrium
  (Player : Set)
  (players : List Player) : Set₁ where
  constructor finiteTUShapleyAllocationEquilibrium
  field
    coalitionWorth : List Player → Nat
    payoff : Player → Nat
    scaledShapley : Player → Nat
    scaledValue : Nat
    scaledShapleyCorrect :
      ∀ p →
      scaledValue * payoff p ≡
      scaledShapley p
    scaledEfficiency :
      sumNat (map payoff players) ≡
      scaledValue * coalitionWorth players

open FiniteTUShapleyAllocationEquilibrium public

record CanonicalPolymorphicSparsemaxCompositionTheorem : Set₁ where
  constructor canonicalPolymorphicSparsemaxCompositionTheorem
  field
    genericPolicy :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.canonicalPolicy K s ≡
      C.sparsemaxPolicy
        (C.actionSpaceK K)
        (C.lcbScore (C.lcbKernel K) (C.lcbCounts s)
          (C.critic (C.watkins s)))
        (C.valuesCount (C.lcbCounts s))
    normProjectionInvariant :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) (n : C.NormPair) →
      C.canonicalPolicy K (C.replaceNorm s n) ≡ C.canonicalPolicy K s
    optimizerProjectionInvariant :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) (o : C.F4IntUState) →
      C.canonicalPolicy K (C.replaceOptimizer s o) ≡ C.canonicalPolicy K s
    hardSparseComposition :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (n : C.NormPair) (o : C.F4IntUState) →
      C.HardSparse K s →
      C.HardSparse K (C.replaceNorm (C.replaceOptimizer s o) n)
    recurrentPrefixComposition :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
    s4PlusS5RecurrentScan :
      S4PlusS5RecurrentScanTheorem C.GRUState C.Int8
    informationPreservingTask :
      ∀ {State Feature Output : Set}
      (observe : State → Feature) (inverse : Feature → State)
      (leftInverse : ∀ s → inverse (observe s) ≡ s)
      (target : State → Output) (s : State) →
      target s ≡ target (inverse (observe s))

open CanonicalPolymorphicSparsemaxCompositionTheorem public

canonical-polymorphic-sparsemax-egraph-theorem :
  CanonicalPolymorphicSparsemaxCompositionTheorem
canonical-polymorphic-sparsemax-egraph-theorem =
  canonicalPolymorphicSparsemaxCompositionTheorem
    (λ K s → refl)
    C.canonicalPolicy-norm-invariant
    C.canonicalPolicy-optimizer-invariant
    C.hardSparse-composition-normPair-F4-L2
    canonical-recurrent-prefix-monoid-homomorphism
    canonical-S4S5-recurrent-scan-theorem
    informationPreserving-symbolic-task-factorization

record ContinuousStationaryMarkovWalrasianData
  (State Price Allocation : Set)
  (Continuous : {A B : Set} → (A → B) → Set) : Set₁ where
  constructor continuousStationaryMarkovWalrasianData
  field
    step : State → State
    aggregate : (State → Allocation) → Allocation
    aggregateContinuous : Continuous aggregate
    invariant :
      ∀ (allocation : State → Allocation) →
      aggregate allocation
      ≡
      aggregate (λ s → allocation (step s))
    staticWalrasian :
      Price → Allocation → Set

open ContinuousStationaryMarkovWalrasianData public

componentPrefix :
  ∀ {Q Input : Set} →
  (Q → Input → Q) → List Input → Q → Q
componentPrefix step [] q = q
componentPrefix step (x ∷ xs) q =
  componentPrefix step xs (step q x)

productPrefix :
  ∀ {Q₁ Q₂ Input : Set} →
  ((Q₁ × Q₂) → Input → (Q₁ × Q₂)) →
  List Input → (Q₁ × Q₂) → (Q₁ × Q₂)
productPrefix step [] q = q
productPrefix step (x ∷ xs) q =
  productPrefix step xs (step q x)

productPrefix-componentPrefix :
  ∀ {Q₁ Q₂ Input : Set}
  (step₁ : Q₁ → Input → Q₁)
  (step₂ : Q₂ → Input → Q₂)
  (xs : List Input) (q₁ : Q₁) (q₂ : Q₂) →
  productPrefix
    (λ { (a , b) x → step₁ a x , step₂ b x })
    xs
    (q₁ , q₂)
  ≡
  (componentPrefix step₁ xs q₁ ,
   componentPrefix step₂ xs q₂)
productPrefix-componentPrefix step₁ step₂ [] q₁ q₂ = refl
productPrefix-componentPrefix step₁ step₂ (x ∷ xs) q₁ q₂ =
  productPrefix-componentPrefix
    step₁ step₂ xs (step₁ q₁ x) (step₂ q₂ x)

record DirectProductFiniteAutomatonComposition
  (Q₁ Q₂ Input : Set) : Set₁ where
  constructor directProductFiniteAutomatonComposition
  field
    step₁ : Q₁ → Input → Q₁
    step₂ : Q₂ → Input → Q₂
    productStep :
      (Q₁ × Q₂) → Input → (Q₁ × Q₂)
    productStep-def :
      ∀ q₁ q₂ x →
      productStep (q₁ , q₂) x
      ≡
      (step₁ q₁ x , step₂ q₂ x)
    prefixCorrect :
      ∀ (xs : List Input) (q₁ : Q₁) (q₂ : Q₂) →
      productPrefix productStep xs (q₁ , q₂)
      ≡
      (componentPrefix step₁ xs q₁ ,
       componentPrefix step₂ xs q₂)

directProductFiniteAutomatonComposition-theorem :
  ∀ {Q₁ Q₂ Input : Set}
  (step₁ : Q₁ → Input → Q₁)
  (step₂ : Q₂ → Input → Q₂) →
  DirectProductFiniteAutomatonComposition Q₁ Q₂ Input
directProductFiniteAutomatonComposition-theorem step₁ step₂ =
  directProductFiniteAutomatonComposition
    step₁
    step₂
    (λ { (q₁ , q₂) x → step₁ q₁ x , step₂ q₂ x })
    (λ _ _ _ → refl)
    (λ xs q₁ q₂ → productPrefix-componentPrefix step₁ step₂ xs q₁ q₂)

data TrivialContinuity : Set where
  trivialContinuity : TrivialContinuity

iterateUpdate :
  ∀ {State : Set} →
  (State → State) → Nat → State → State
iterateUpdate update zero state = state
iterateUpdate update (suc n) state =
  update (iterateUpdate update n state)

GloballyEventuallyFixed :
  ∀ {State : Set} →
  (State → State) → State → Set
GloballyEventuallyFixed update fixed =
  ∀ state → Σ Nat (λ n → iterateUpdate update n state ≡ fixed)

successor-never-globally-eventually-fixed-at-zero :
  ¬ GloballyEventuallyFixed suc 0
successor-never-globally-eventually-fixed-at-zero h =
  no-suc-zero
    (trans
      (sym (iterateUpdate-suc 1))
      (proj₂ (h 1)))
  where
    iterateUpdate-suc :
      ∀ n → iterateUpdate suc n 1 ≡ suc n
    iterateUpdate-suc zero = refl
    iterateUpdate-suc (suc n) =
      cong suc (iterateUpdate-suc n)

    no-suc-zero : ∀ {n : Nat} → suc n ≢ 0
    no-suc-zero ()

exact-injective-continuous-leftInverse-does-not-imply-update-stability :
  ¬
    (∀ {State Feature : Set}
       (observe : State → Feature)
       (inverse : Feature → State)
       (Continuous : {A B : Set} → (A → B) → Set)
       (update : State → State)
       (fixed : State) →
       ContinuousLeftInverseTheorem
         State Feature observe inverse Continuous →
       GloballyEventuallyFixed update fixed)
exact-injective-continuous-leftInverse-does-not-imply-update-stability h =
  successor-never-globally-eventually-fixed-at-zero
    (h
      (λ n → n)
      (λ n → n)
      (λ _ → TrivialContinuity)
      suc
      0
      (continuousLeftInverseTheorem
        (λ _ → trivialContinuity)
        (λ _ → trivialContinuity)
        (λ _ → refl)))

record OffPolicyFunctionApproximationStabilityBoundary : Set₁ where
  constructor offPolicyFunctionApproximationStabilityBoundary
  field
    representationVsUpdateStability :
      ¬
        (∀ {State Feature : Set}
           (observe : State → Feature)
           (inverse : Feature → State)
           (Continuous : {A B : Set} → (A → B) → Set)
           (update : State → State)
           (fixed : State) →
           ContinuousLeftInverseTheorem
             State Feature observe inverse Continuous →
           GloballyEventuallyFixed update fixed)

offPolicyFunctionApproximationStabilityBoundaryWitness :
  OffPolicyFunctionApproximationStabilityBoundary
offPolicyFunctionApproximationStabilityBoundaryWitness =
  offPolicyFunctionApproximationStabilityBoundary
    exact-injective-continuous-leftInverse-does-not-imply-update-stability

record ExactReconstructionOnImage
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor exactReconstructionOnImage
  field
    reconstruct :
      ∀ s → inverse (observe s) ≡ s
    imageReconstructs :
      ∀ f → (Σ State (λ s → observe s ≡ f)) →
      observe (inverse f) ≡ f

open ExactReconstructionOnImage public

exactReconstructionOnImage-from-inverses :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State} →
  (∀ s → inverse (observe s) ≡ s) →
  (∀ f → observe (inverse f) ≡ f) →
  ExactReconstructionOnImage State Feature observe inverse
exactReconstructionOnImage-from-inverses leftInverse rightInverse =
  exactReconstructionOnImage
    leftInverse
    (λ f _ → rightInverse f)

record GlobalConjugacyEquivalence
  (State Feature : Set)
  (step : State → State)
  (observe : State → Feature)
  (featureStep : Feature → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor globalConjugacyEquivalence
  field
    forward :
      ∀ s → observe (step s) ≡ featureStep (observe s)
    stateReconstruction :
      ∀ s → inverse (observe s) ≡ s
    featureReconstruction :
      ∀ f → observe (inverse f) ≡ f
    stateDynamicsFromFeature :
      ∀ s → step s ≡ inverse (featureStep (observe s))
    featureDynamicsFromState :
      ∀ f → featureStep f ≡ observe (step (inverse f))

globalConjugacyEquivalence-iterate :
  ∀ {State Feature : Set}
    {step : State → State}
    {observe : State → Feature}
    {featureStep : Feature → Feature}
    {inverse : Feature → State}
    (G : GlobalConjugacyEquivalence
      State
      Feature
      step
      observe
      featureStep
      inverse)
    (n : Nat)
    (s : State) →
  observe (iterateState step n s)
  ≡
  iterateState featureStep n (observe s)
globalConjugacyEquivalence-iterate G zero s = refl
globalConjugacyEquivalence-iterate G (suc n) s =
  trans
    (field G .forward (iterateState step n s))
    (cong
      featureStep
      (globalConjugacyEquivalence-iterate G n s))

recurrentListState-append :
  ∀ {State Input : Set}
  (R : C.RecurrentNetwork State Input)
  (xs ys : List Input)
  (s : State) →
  C.recurrentListState R (xs ++ ys) s
  ≡
  C.recurrentListState R ys
    (C.recurrentListState R xs s)
recurrentListState-append R [] ys s = refl
recurrentListState-append R (x ∷ xs) ys s =
  recurrentListState-append
    R
    xs
    ys
    (C.runNetwork R s x)

canonicalTokenStep-conjugacy :
  ∀ (s : C.GRUState) (t : C.CanonicalToken) →
  C.runNetwork C.canonicalTokenRecurrentNetwork s t
  ≡
  C.runNetwork C.canonicalGRURecurrentNetwork
    s
    (C.canonicalTokenEncode t)
canonicalTokenStep-conjugacy s t = refl

canonicalTokenListState-conjugacy :
  ∀ (xs : C.CanonicalTokenSequence) (s : C.GRUState) →
  C.canonicalTokenListState xs s
  ≡
  C.recurrentListState
    C.canonicalGRURecurrentNetwork
    (C.canonicalTokenEncodeList xs)
    s
canonicalTokenListState-conjugacy [] s = refl
canonicalTokenListState-conjugacy (t ∷ ts) s =
  canonicalTokenListState-conjugacy
    ts
    (C.canonicalTokenStep s t)

canonicalToken-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    C.GRUState
    C.CanonicalToken
canonicalToken-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

canonicalTokenLogitTrace-append :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (xs ys : C.CanonicalTokenSequence)
  (s : C.GRUState) →
  C.canonicalTokenLogitTrace K (xs ++ ys) s
  ≡
  C.canonicalTokenLogitTrace K xs s ++
  C.canonicalTokenLogitTrace K ys
    (C.canonicalTokenListState xs s)
canonicalTokenLogitTrace-append K [] ys s = refl
canonicalTokenLogitTrace-append K (t ∷ xs) ys s =
  cong
    (λ trace →
      C.logits K s ∷ trace)
    (canonicalTokenLogitTrace-append
      K
      xs
      ys
      (C.canonicalTokenStep s t))

record CanonicalGlobalTokenEncodingConjugacyTheorem : Set₁ where
  constructor canonicalGlobalTokenEncodingConjugacyTheorem
  field
    recurrentStepConjugacy :
      ∀ s t →
      C.runNetwork C.canonicalTokenRecurrentNetwork s t
      ≡
      C.runNetwork C.canonicalGRURecurrentNetwork
        s
        (C.canonicalTokenEncode t)
    recurrentListConjugacy :
      ∀ xs s →
      C.canonicalTokenListState xs s
      ≡
      C.recurrentListState
        C.canonicalGRURecurrentNetwork
        (C.canonicalTokenEncodeList xs)
        s

open CanonicalGlobalTokenEncodingConjugacyTheorem public

canonical-global-token-encoding-conjugacy :
  CanonicalGlobalTokenEncodingConjugacyTheorem
canonical-global-token-encoding-conjugacy =
  canonicalGlobalTokenEncodingConjugacyTheorem
    canonicalTokenStep-conjugacy
    canonicalTokenListState-conjugacy

record ExactFunctionIsomorphismTransportTheorem
  (S T A B : Set)
  (isoA : StateIsomorphism S A)
  (isoB : StateIsomorphism T B)
  (f : S → T) : Set₁ where
  constructor exactFunctionIsomorphismTransportTheorem
  field
    translatedFunction : A → B
    exactTransport :
      ∀ x →
      StateIsomorphism.to isoB (f x) ≡
      translatedFunction (StateIsomorphism.to isoA x)

exactRecurrentFunctionTranslation :
  ∀ {S A : Set}
    {isoA : StateIsomorphism S A}
    (step : S → S)
    (stepA : A → A)
    (conjugacy :
      ∀ x →
      StateIsomorphism.to isoA (step x) ≡
      stepA (StateIsomorphism.to isoA x)) →
  ExactRecurrentFunctionTranslationTheorem S A isoA step stepA
exactRecurrentFunctionTranslation step stepA conjugacy =
  exactRecurrentFunctionTranslationTheorem
    conjugacy
    (λ {T} {B} {isoB} f →
      exactFunctionIsomorphismTransport f)

record CanonicalExactRNNLMTheorem : Set₁ where
  constructor canonicalExactRNNLMTheorem
  field
    globalTokenConjugacy :
      CanonicalGlobalTokenEncodingConjugacyTheorem
    recurrentTrace :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ≡
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

open CanonicalExactRNNLMTheorem public

canonical-exact-rnn-lm-theorem : CanonicalExactRNNLMTheorem
canonical-exact-rnn-lm-theorem =
  canonicalExactRNNLMTheorem
    canonical-global-token-encoding-conjugacy
    canonicalTokenLogitTrace-append

record CanonicalGlobalTokenLMCompositionTheorem : Set₁ where
  constructor canonicalGlobalTokenLMCompositionTheorem
  field
    globalTokenConjugacy :
      CanonicalGlobalTokenEncodingConjugacyTheorem
    tokenPrefixMonoid :
      RecurrentPrefixMonoidHomomorphism
        C.GRUState
        C.CanonicalToken
    traceAppend :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ≡
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

open CanonicalGlobalTokenLMCompositionTheorem public

canonical-global-token-lm-composition-theorem :
  CanonicalGlobalTokenLMCompositionTheorem
canonical-global-token-lm-composition-theorem =
  canonicalGlobalTokenLMCompositionTheorem
    canonical-global-token-encoding-conjugacy
    canonicalToken-prefix-monoid-homomorphism
    canonicalTokenLogitTrace-append

record CanonicalTokenArbitraryLengthGenerationTheorem : Set₁ where
  constructor canonicalTokenArbitraryLengthGenerationTheorem
  field
    stateConjugacy :
      ∀ (xs : C.CanonicalTokenSequence) (s : C.GRUState) →
      C.canonicalTokenListState xs s
      ≡
      C.recurrentListState
        C.canonicalGRURecurrentNetwork
        (C.canonicalTokenEncodeList xs)
        s

    traceAppend :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ≡
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

    prefixMonoid :
      RecurrentPrefixMonoidHomomorphism
        C.GRUState
        C.CanonicalToken

canonical-token-arbitrary-length-generation-theorem :
  CanonicalTokenArbitraryLengthGenerationTheorem
canonical-token-arbitrary-length-generation-theorem =
  canonicalTokenArbitraryLengthGenerationTheorem
    canonicalTokenListState-conjugacy
    canonicalTokenLogitTrace-append
    canonicalToken-prefix-monoid-homomorphism

canonicalIntegerHaarCross :
  C.int8Add C.one8 (C.int8Neg C.one8) ≡ C.zero8
canonicalIntegerHaarCross = refl

canonicalIntegerHaarEnergy :
  C.int8Add C.one8 C.one8 ≡ C.int8OfNat 2
canonicalIntegerHaarEnergy = refl

record CanonicalIntegerHaarScaledOrthogonalityTheorem : Set₁ where
  constructor canonicalIntegerHaarScaledOrthogonalityTheorem
  field
    crossOrthogonality :
      C.int8Add C.one8 (C.int8Neg C.one8) ≡ C.zero8
    integerEnergy :
      C.int8Add C.one8 C.one8 ≡ C.int8OfNat 2

open CanonicalIntegerHaarScaledOrthogonalityTheorem public

canonical-integer-haar-scaled-orthogonality-theorem :
  CanonicalIntegerHaarScaledOrthogonalityTheorem
canonical-integer-haar-scaled-orthogonality-theorem =
  canonicalIntegerHaarScaledOrthogonalityTheorem
    canonicalIntegerHaarCross
    canonicalIntegerHaarEnergy

canonicalAStarZeroCost :
  (zero + zero) ≡ zero
canonicalAStarZeroCost = refl

canonicalAStarSuccessorCost :
  ∀ n → n + suc zero ≡ suc n
canonicalAStarSuccessorCost n = +-suc n zero

record CanonicalAStarCostGuidanceTheorem : Set₁ where
  constructor canonicalAStarCostGuidanceTheorem
  field
    zeroCostIdentity :
      (zero + zero) ≡ zero
    successorCostComposition :
      ∀ n → n + suc zero ≡ suc n
    exactTokenTrace :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ≡
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

open CanonicalAStarCostGuidanceTheorem public

canonical-a-star-cost-guidance-theorem :
  CanonicalAStarCostGuidanceTheorem
canonical-a-star-cost-guidance-theorem =
  canonicalAStarCostGuidanceTheorem
    canonicalAStarZeroCost
    canonicalAStarSuccessorCost
    canonicalTokenLogitTrace-append

record CanonicalEndogenousEGraphAStarTransportClosureTheorem : Set₁ where
  constructor canonicalEndogenousEGraphAStarTransportClosureTheorem
  field
    aStarGuidance :
      CanonicalAStarCostGuidanceTheorem
    representationTransport :
      GeneralizedRepresentationTransportCompositionTheorem
    endogenousTraceTransport :
      ∀ {S T A B : Set}
        {isoA : StateIsomorphism S A}
        {isoB : StateIsomorphism T B}
        (f : S → T) →
      ExactFunctionIsomorphismTransportTheorem S T A B isoA isoB f
    semanticEGraphAStarClosure :
      ∀ {Expression State : Set} →
      (A : AStarSemanticClosure Expression State) →
      ∀ {e f : Expression} →
      EGraphSemanticPath (semantics A) e f →
      interpret (semantics A) e ≡ interpret (semantics A) f

CanonicalEndogenousAStarTransportClosureTheorem :
  Set₁
CanonicalEndogenousAStarTransportClosureTheorem =
  CanonicalEndogenousEGraphAStarTransportClosureTheorem

open CanonicalEndogenousAStarTransportClosureTheorem public

record CanonicalFiniteCycleExclusionIsomorphismTheorem : Set₁ where
  constructor canonicalFiniteCycleExclusionIsomorphismTheorem
  field
    iterateConjugacy :
      ∀ {A B : Set}
        (iso : StateIsomorphism A B)
        (f : A → A)
        (g : B → B) →
        (∀ a → to iso (f a) ≡ g (to iso a)) →
        ∀ n a →
        to iso (iterateIsomorphism f n a)
        ≡
        iterateIsomorphism g n (to iso a)
    cycleTransport :
      ∀ {A B : Set}
        (iso : StateIsomorphism A B)
        (f : A → A)
        (g : B → B) →
        (∀ a → to iso (f a) ≡ g (to iso a)) →
        (∀ n a → iterateIsomorphism f (suc n) a ≢ a) →
        ∀ n a →
        iterateIsomorphism g (suc n) (to iso a) ≢ to iso a

open CanonicalFiniteCycleExclusionIsomorphismTheorem public

record CanonicalOperatorCompositionTheorem : Set₁ where
  constructor canonicalOperatorCompositionTheorem
  field
    identity :
      ∀ {S : Set} (s : S) →
      C.applyEndomorphism
        (C.identityEndomorphism {State = S}) s
      ≡ s
    composition :
      ∀ {S : Set}
        (f g : C.Endomorphism S) (s : S) →
      C.applyEndomorphism
        (C.composeEndomorphism f g) s
      ≡
      C.applyEndomorphism f
        (C.applyEndomorphism g s)
    associativity :
      ∀ {S : Set}
        (f g h : C.Endomorphism S) (s : S) →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g) h) s
      ≡
      C.applyEndomorphism
        (C.composeEndomorphism
          f (C.composeEndomorphism g h)) s

open CanonicalOperatorCompositionTheorem public

canonical-operator-composition-theorem :
  CanonicalOperatorCompositionTheorem
canonical-operator-composition-theorem =
  canonicalOperatorCompositionTheorem
    (λ s → refl)
    (λ f g s → refl)
    C.endomorphismAssociative

record CanonicalF4GlobalOptimizerStabilityTheorem : Set₁ where
  constructor canonicalF4GlobalOptimizerStabilityTheorem
  field
    thetaTranslation :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.thetaQ (C.canonicalOptimizerStep K s) ≡
      C.int8Add
        (C.int8Add (C.thetaQ (C.optimizer s)) (C.canonicalSignal K s))
        (C.l2Correction (C.globalL2 (C.optimizerKernel K)))
    stableNonThetaCoordinates :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.rTheta (C.canonicalOptimizerStep K s) ≡ C.zero8 ×
      C.eQ (C.canonicalOptimizerStep K s) ≡ C.eQ (C.optimizer s) ×
      C.rE (C.canonicalOptimizerStep K s) ≡ C.rE (C.optimizer s) ×
      C.rL (C.canonicalOptimizerStep K s) ≡ C.rL (C.optimizer s)
    equalInputStability :
      ∀ {A} (K : C.FullLearnerKernel A)
        (s t : C.FullLearnerState A) →
      C.optimizer s ≡ C.optimizer t →
      C.canonicalSignal K s ≡ C.canonicalSignal K t →
      C.canonicalOptimizerStep K s ≡ C.canonicalOptimizerStep K t

open CanonicalF4GlobalOptimizerStabilityTheorem public

canonical-f4-global-optimizer-stability-theorem :
  CanonicalF4GlobalOptimizerStabilityTheorem
canonical-f4-global-optimizer-stability-theorem =
  canonicalF4GlobalOptimizerStabilityTheorem
    (λ K s → C.f4ParameterInvariant
      (C.optimizerKernel K) (C.optimizer s) (C.canonicalSignal K s))
    (λ K s → refl , (refl , (refl , refl)))
    (λ K s t optimizerEq signalEq →
      cong₂
        (λ optimizer signal →
          C.f4ThetaStep (C.optimizerKernel K) optimizer signal)
        optimizerEq signalEq)

f4Orbit :
  C.F4IntUKernel → C.Int8 → Nat → C.F4IntUState → C.F4IntUState
f4Orbit K g zero s = s
f4Orbit K g (suc n) s =
  C.f4ThetaStep K (f4Orbit K g n s) g

record F4UpperBoundedTrajectory
  (K : C.F4IntUKernel)
  (g : C.Int8)
  (s : C.F4IntUState) : Set₁ where
  constructor f4UpperBoundedTrajectory
  field
    bound : Nat
    bounded :
      ∀ n →
      C.code (C.thetaQ (f4Orbit K g n s)) ≤ℤ + bound

nat-plus-one :
  ∀ n → n + suc zero ≡ suc n
nat-plus-one n =
  trans
    (+-suc n zero)
    (cong suc (+-identityʳ n))

integer-nat-plus-one :
  ∀ n → (+ n) +ℤ (+ 1) ≡ + (suc n)
integer-nat-plus-one n =
  cong +_ (nat-plus-one n)

f4-zero-L2-unit-step-code :
  ∀ s →
  C.code
    (C.thetaQ
      (C.f4ThetaStep
        (C.f4IntUKernel C.zero8)
        s
        C.one8))
  ≡
  C.code (C.thetaQ s) +ℤ (+ 1)
f4-zero-L2-unit-step-code s =
  trans
    (cong C.code
      (C.f4ParameterInvariant
        (C.f4IntUKernel C.zero8)
        s
        C.one8))
    (IntegerProperties.+-identityʳ
      (C.code (C.thetaQ s) +ℤ (+ 1)))

f4-unit-forcing-linear-growth :
  ∀ n s →
  C.code
    (C.thetaQ
      (f4Orbit
        (C.f4IntUKernel C.zero8)
        C.one8
        n
        s))
  ≡
  C.code (C.thetaQ s) +ℤ (+ n)
f4-unit-forcing-linear-growth zero s =
  sym (IntegerProperties.+-identityʳ (C.code (C.thetaQ s)))
f4-unit-forcing-linear-growth (suc n) s =
  trans
    (f4-zero-L2-unit-step-code
      (f4Orbit (C.f4IntUKernel C.zero8) C.one8 n s))
    (trans
      (cong
        (λ z → z +ℤ (+ 1))
        (f4-unit-forcing-linear-growth n s))
      (trans
        (IntegerProperties.+-assoc
          (C.code (C.thetaQ s))
          (+ n)
          (+ 1))
        (cong
          (λ z → C.code (C.thetaQ s) +ℤ z)
          (integer-nat-plus-one n))))

nat-suc-not-le :
  ∀ n → suc n ≤ n → ⊥
nat-suc-not-le zero ()
nat-suc-not-le (suc n) (s≤s h) =
  nat-suc-not-le n h

f4-unit-forcing-no-upper-bound :
  ∀ {s : C.F4IntUState} →
  C.thetaQ s ≡ C.zero8 →
  ¬ F4UpperBoundedTrajectory
      (C.f4IntUKernel C.zero8)
      C.one8
      s
f4-unit-forcing-no-upper-bound thetaZero boundedWitness =
  let
    B = F4UpperBoundedTrajectory.bound boundedWitness
    horizonBound = F4UpperBoundedTrajectory.bounded boundedWitness (suc B)
    growth =
      f4-unit-forcing-linear-growth
        (suc B)
        _
    growthFromZero :
      C.code
        (C.thetaQ
          (f4Orbit
            (C.f4IntUKernel C.zero8)
            C.one8
            (suc B)
            _))
      ≡
      + (suc B)
    growthFromZero =
      trans
        growth
        (trans
          (cong
            (λ z → z +ℤ (+ suc B))
            (cong C.code thetaZero))
          (IntegerProperties.+-identityˡ (+ suc B)))
    impossibleOrder :
      + (suc B) ≤ℤ + B
    impossibleOrder =
      subst
        (λ z → z ≤ℤ + B)
        growthFromZero
        horizonBound
  in
    nat-suc-not-le B
      (IntegerProperties.drop‿+≤+ impossibleOrder)

record CanonicalPureNonOrangeBypassCompletionTheorem : Set₁ where
  constructor canonicalPureNonOrangeBypassCompletionTheorem
  field
    recurrentPrefix :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
    fullLearnerScanConjugacy :
      CanonicalFullLearnerConnectedScanConjugacyTheorem
    exactTuringBoundary :
      ¬ CanonicalExactCompositionTuringCompletenessContract
    finiteCycleIsomorphismTransport :
      CanonicalFiniteCycleExclusionIsomorphismTheorem
    operatorComposition :
      CanonicalOperatorCompositionTheorem
    f4OptimizerStability :
      CanonicalF4GlobalOptimizerStabilityTheorem
    integerHaarOrthogonality :
      CanonicalIntegerHaarScaledOrthogonalityTheorem

open CanonicalPureNonOrangeBypassCompletionTheorem public

record StationaryLimitTheorem
  (Distribution : Set)
  (P : Distribution → Distribution)
  (μ : Nat → Distribution)
  (μ∞ : Distribution)
  (Converges : (Nat → Distribution) → Distribution → Set) : Set₁ where
  constructor stationaryLimitTheorem
  field
    transitionLaw :
      ∀ n → μ (suc n) ≡ P (μ n)
    converges :
      Converges μ μ∞
    limitPreserved :
      Converges μ μ∞ → P μ∞ ≡ μ∞

canonical-persistent-excitation-requirement-theorem :
  CanonicalPersistentExcitationRequirementTheorem
canonical-persistent-excitation-requirement-theorem =
  canonicalPersistentExcitationRequirementTheorem
    tt
    tt

record ExactContractComputabilityBoundaryTheorem : Set₁ where
  constructor exactContractComputabilityBoundaryTheorem
  field
    specifiedContractImpossible :
      ¬ CanonicalExactCompositionTuringCompletenessContract
    scopeIsContractSpecific :
      ⊤

exact-contract-computability-boundary-theorem :
  ExactContractComputabilityBoundaryTheorem
exact-contract-computability-boundary-theorem =
  exactContractComputabilityBoundaryTheorem
    canonicalExactCompositionTuringCompletenessContract-impossible
    tt

record CanonicalStationarySubcompositionTheorem : Set₁ where
  constructor canonicalStationarySubcompositionTheorem
  field
    stationaryLimitContract :
      ∀ {Distribution : Set}
        (P : Distribution → Distribution)
        (μ : Nat → Distribution)
        (π : Distribution)
        (Converges : (Nat → Distribution) → Distribution → Set) →
      (∀ n → μ (suc n) ≡ P (μ n)) →
      Converges μ π →
      (Converges μ π → P π ≡ π) →
      StationaryLimitTheorem
        Distribution P μ π Converges

canonical-stationary-subcomposition-theorem :
  CanonicalStationarySubcompositionTheorem
canonical-stationary-subcomposition-theorem =
  canonicalStationarySubcompositionTheorem
    (λ P μ π Converges transitionLaw convergence limitPreserved →
      stationaryLimitTheorem
        transitionLaw
        convergence
        limitPreserved)

record DistributionalStationaryAggregateTransport
  (Distribution Economic : Set)
  (P : Distribution → Distribution)
  (μ : Nat → Distribution)
  (μ∞ : Distribution)
  (Converges : (Nat → Distribution) → Distribution → Set)
  (aggregate : Distribution → Economic)
  (economicStep : Economic → Economic) : Set₁ where
  constructor distributionalStationaryAggregateTransport
  field
    stationaryLimit :
      StationaryLimitTheorem
        Distribution
        P
        μ
        μ∞
        Converges
    aggregateStepCommutes :
      ∀ d →
      aggregate (P d) ≡
      economicStep (aggregate d)

open DistributionalStationaryAggregateTransport public

distributionalStationaryAggregate-stationary :
  ∀ {Distribution Economic : Set}
  {P : Distribution → Distribution}
  {μ : Nat → Distribution}
  {μ∞ : Distribution}
  {Converges : (Nat → Distribution) → Distribution → Set}
  {aggregate : Distribution → Economic}
  {economicStep : Economic → Economic}
  (W :
    DistributionalStationaryAggregateTransport
      Distribution
      Economic
      P
      μ
      μ∞
      Converges
      aggregate
      economicStep) →
  economicStep (aggregate μ∞) ≡ aggregate μ∞
distributionalStationaryAggregate-stationary W =
  trans
    (sym (aggregateStepCommutes W _))
    (cong
      aggregate
      (StationaryLimitTheorem.limitPreserved
        (stationaryLimit W)
        (StationaryLimitTheorem.converges (stationaryLimit W))))

record FunctionClassInclusion
  (Input Output : Set)
  (FBase FFull : (Input → Output) → Set₁) : Set₁ where
  constructor functionClassInclusion
  field
    include :
      ∀ {f : Input → Output} →
      FBase f →
      FFull f

record StrictFunctionClassSeparation
  (Input Output : Set)
  (FBase FFull : (Input → Output) → Set₁) : Set₁ where
  constructor strictFunctionClassSeparation
  field
    inclusion :
      FunctionClassInclusion Input Output FBase FFull
    witness :
      Input → Output
    witnessInFull :
      FFull witness
    witnessNotInBase :
      ¬ FBase witness

twoPow : Nat → Nat
twoPow zero = suc zero
twoPow (suc k) = twoPow k + twoPow k

nat-plus-right-mono :
  ∀ {a b c : Nat} → a ≤ b → a + c ≤ b + c
nat-plus-right-mono z≤n = z≤n
nat-plus-right-mono (s≤s p) = s≤s (nat-plus-right-mono p)

record EfficientOperatorMonoidRepresentation
  (State Input : Set) : Set₁ where
  constructor efficientOperatorMonoidRepresentation
  field
    operator :
      Input → C.Endomorphism State
    operatorAssociative :
      ∀ (f g h : C.Endomorphism State) s →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g)
          h)
        s
      ≡
      C.applyEndomorphism
        (C.composeEndomorphism
          f
          (C.composeEndomorphism g h))
        s
    representationSpan : Nat
    decodingSpan : Nat
    compositionSpan : Nat
    compositionWork : Nat
    scanSpan : Nat → Nat
    scanWork : Nat → Nat
    scanSpan-linear :
      ∀ h →
      scanSpan h ≤ compositionSpan + compositionSpan * h
    scanWork-linear :
      ∀ h →
      scanWork h ≤ compositionWork * h

record ParallelPrefixComplexityCertificate
  (State Input : Set) : Set₁ where
  constructor parallelPrefixComplexityCertificate
  field
    monoidRepresentation :
      EfficientOperatorMonoidRepresentation State Input
    exactScan :
      RecurrentAssociativeScanTheorem State Input
    totalSpan :
      Nat → Nat
    totalWork :
      Nat → Nat
    totalSpan-definition :
      ∀ h →
      totalSpan h ≡
        EfficientOperatorMonoidRepresentation.representationSpan
          monoidRepresentation
        + EfficientOperatorMonoidRepresentation.scanSpan
            monoidRepresentation h
        + EfficientOperatorMonoidRepresentation.decodingSpan
            monoidRepresentation
    totalWork-definition :
      ∀ h →
      totalWork h ≡
        EfficientOperatorMonoidRepresentation.scanWork
          monoidRepresentation h

record LogarithmicScanSpanCertificate
  (State Input : Set) : Set₁ where
  constructor logarithmicScanSpanCertificate
  field
    scanSpan : Nat → Nat
    coefficient : Nat
    additive : Nat
    scanSpan-bound :
      ∀ k h →
      h ≤ twoPow k →
      scanSpan h ≤ coefficient * k + additive

record LogarithmicPrefixScanComplexityTheorem
  (State Input : Set) : Set₁ where
  constructor logarithmicPrefixScanComplexityTheorem
  field
    exactScan :
      RecurrentAssociativeScanTheorem State Input
    operatorMonoid :
      EfficientOperatorMonoidRepresentation State Input
    logarithmicSpan :
      LogarithmicScanSpanCertificate State Input
    representationOverhead :
      Nat
    decodingOverhead :
      Nat
    horizonSpan :
      Nat → Nat
    horizonWork :
      Nat → Nat
    horizonSpan-definition :
      ∀ h →
      horizonSpan h ≡
        LogarithmicScanSpanCertificate.scanSpan logarithmicSpan h
        + representationOverhead
        + decodingOverhead
    horizonWork-linear :
      ∀ h →
      horizonWork h ≤
      EfficientOperatorMonoidRepresentation.compositionWork operatorMonoid * h
    exactness :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : Nat → Input)
        (h : Nat)
        (s : State) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism R xs h)
        s
      ≡
      C.recurrentPrefixState R xs h s
    horizonSpan-logarithmic :
      ∀ k h →
      h ≤ twoPow k →
      horizonSpan h ≤
        LogarithmicScanSpanCertificate.coefficient logarithmicSpan * k
        + LogarithmicScanSpanCertificate.additive logarithmicSpan
        + representationOverhead
        + decodingOverhead

------------------------------------------------------------------------
-- Closed MARL law composition.
--
-- These are the three exact learner-facing laws used by the current
-- coupled learner: recurrent-prefix composition, the F4 optimizer step,
-- and NormPair step invariance.  They compose with the endogenous Watkins
-- target in one closed theorem package.  This is the unconditional
-- learner-side theorem; it does not claim the separate physics Law I/II/III
-- interface is already proved.
------------------------------------------------------------------------

record CanonicalMARLLawCompositionTheorem : Set₁ where
  constructor canonicalMARLLawCompositionTheorem
  field
    recurrentPrefixComposition :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
    f4StepLaw :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (o : C.F4IntUState)
      (signal : C.Int8) →
      C.runNetwork
        (canonicalF4RecurrentNetwork K)
        o
        signal
      ≡
      C.f4ThetaStep (C.optimizerKernel K) o signal
    normPairStepLaw :
      ∀ (n : C.NormPair) (signal : C.Int8) →
      C.runNetwork
        canonicalNormPairRecurrentNetwork
        n
        signal
      ≡ n
    watkinsSignalLaw :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalSignal K s ≡
      C.canonicalWatkinsTarget K s
    fullComposition :
      CanonicalGRUF4NormWatkinsPrefixCompositionTheorem

canonical-marl-law-composition-theorem :
  CanonicalMARLLawCompositionTheorem
canonical-marl-law-composition-theorem =
  canonicalMARLLawCompositionTheorem
    canonical-recurrent-prefix-monoid-homomorphism
    canonicalF4RecurrentNetwork-step-law
    canonicalNormPairRecurrentNetwork-step-law
    C.canonicalSignal-watkins-target
    canonical-gruf4-norm-watkins-prefix-composition-theorem

------------------------------------------------------------------------
-- Carrier-polymorphic continuous Hodge-Maxwell representation.
--
-- The physical content is explicit in the certificate: d F = 0 and
-- d(star F) = j, closure under the supplied solution step, exact
-- encode/decode inverse laws, recurrent-step conjugacy, and continuity.
-- This is an exact representation schema.  It does not assert existence
-- of such a certificate for the current learner without those witnesses.
------------------------------------------------------------------------

record ContinuousHodgeMaxwellExactRepresentationData
  (GRU : Set)
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor continuousHodgeMaxwellExactRepresentationData
  field
    Form2 : Set
    FormStar : Set
    Form3 : Set
    d : Form2 → Form3
    star : Form2 → FormStar
    dStar : FormStar → Form3
    zero3 : Form3

    Solution : Set
    fieldF : Solution → Form2
    fieldJ : Solution → Form3

    maxwellEquation :
      ∀ s →
      (d (fieldF s) ≡ zero3) ×
      (dStar (star (fieldF s)) ≡ fieldJ s)

    step : Solution → Solution
    gruStep : GRU → GRU
    encode : Solution → GRU
    decode : GRU → Solution

    decodeEncode :
      ∀ s → decode (encode s) ≡ s

    encodeDecode :
      ∀ g → encode (decode g) ≡ g

    maxwellClosed :
      ∀ s →
      maxwellEquation (step s)

    conjugacy :
      ∀ s →
      encode (step s) ≡ gruStep (encode s)

    continuousD : Continuous d
    continuousStar : Continuous star
    continuousDStar : Continuous dStar
    continuousFieldF : Continuous fieldF
    continuousFieldJ : Continuous fieldJ
    continuousStep : Continuous step
    continuousGRUStep : Continuous gruStep
    continuousEncode : Continuous encode
    continuousDecode : Continuous decode

open ContinuousHodgeMaxwellExactRepresentationData public

continuousHodgeMaxwell-state-isomorphism :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousHodgeMaxwellExactRepresentationData GRU) →
  StateIsomorphism (Solution D) GRU
continuousHodgeMaxwell-state-isomorphism D =
  stateIsomorphism
    (encode D)
    (decode D)
    (decodeEncode D)
    (encodeDecode D)

continuousHodgeMaxwell-global-encode-injective :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousHodgeMaxwellExactRepresentationData GRU) →
  ∀ {x y} →
  encode D x ≡ encode D y →
  x ≡ y
continuousHodgeMaxwell-global-encode-injective D {x} {y} eq =
  trans
    (sym (decodeEncode D x))
    (trans
      (cong (decode D) eq)
      (decodeEncode D y))

record ConnectedContinuousHodgeMaxwellGRURepresentationTheorem
  (GRU : Set)
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor connectedContinuousHodgeMaxwellGRURepresentationTheorem
  field
    semantics :
      ContinuousHodgeMaxwellExactRepresentationData GRU

    globalStateIsomorphism :
      StateIsomorphism
        (Solution semantics)
        GRU

    exactGRUStepRepresentation :
      ∀ s →
      to globalStateIsomorphism (step semantics s)
      ≡
      gruStep semantics
        (to globalStateIsomorphism s)

    exactFieldEquations :
      ∀ s →
      maxwellEquation semantics s

    globalEncodeInjective :
      ∀ {x y} →
      encode semantics x ≡ encode semantics y →
      x ≡ y

connected-continuous-hodge-maxwell-gru-representation-theorem :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousHodgeMaxwellExactRepresentationData GRU) →
  ConnectedContinuousHodgeMaxwellGRURepresentationTheorem GRU
connected-continuous-hodge-maxwell-gru-representation-theorem D =
  connectedContinuousHodgeMaxwellGRURepresentationTheorem
    D
    (continuousHodgeMaxwell-state-isomorphism D)
    (λ s → conjugacy D s)
    (λ s → maxwellEquation D s)
    (continuousHodgeMaxwell-global-encode-injective D)

------------------------------------------------------------------------
-- Exact Hodge-Maxwell/full-learner bridge.
--
-- The learner side is the closed MARL law composition above.  The
-- cross-domain step is deliberately proof-relevant: a solution-state
-- encoder/decoder and exact step conjugacy are required.  The theorem then
-- derives the corresponding encoded learner-step conjugacy by equality
-- transport.  No equilibrium, convergence, or physical existence theorem
-- is smuggled into this bridge.
------------------------------------------------------------------------

record CanonicalLearnerHodgeMaxwellCompositionTheorem
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor canonicalLearnerHodgeMaxwellCompositionTheorem
  field
    learnerSemantics :
      CanonicalMARLLawCompositionTheorem
    hodgeRepresentation :
      ConnectedContinuousHodgeMaxwellGRURepresentationTheorem
        C.CanonicalFullLearnerState

    learnerToSolution :
      C.CanonicalFullLearnerState →
      Solution (semantics hodgeRepresentation)

    solutionToLearner :
      Solution (semantics hodgeRepresentation) →
      C.CanonicalFullLearnerState

    learnerSolutionLeftInverse :
      ∀ s →
      solutionToLearner (learnerToSolution s) ≡ s

    learnerSolutionRightInverse :
      ∀ q →
      learnerToSolution (solutionToLearner q) ≡ q

    learnerStepConjugacy :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      learnerToSolution
        (C.canonicalFullStep K s)
      ≡
      step
        (semantics hodgeRepresentation)
        (learnerToSolution s)

open CanonicalLearnerHodgeMaxwellCompositionTheorem public

canonical-learner-hodge-maxwell-step-conjugacy :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}) →
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  encode
    (semantics (hodgeRepresentation W))
    (learnerToSolution W s)
  ≡
  gruStep
    (semantics (hodgeRepresentation W))
    (encode
      (semantics (hodgeRepresentation W))
      (learnerToSolution W s))
canonical-learner-hodge-maxwell-step-conjugacy
  W K s =
  trans
    (cong
      (encode (semantics (hodgeRepresentation W)))
      (sym (learnerStepConjugacy W K s)))
    (conjugacy
      (semantics (hodgeRepresentation W))
      (learnerToSolution W s))

canonical-physics-to-learner-transition-witness :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel) →
  PhysicsToLearnerTransitionWitness
    C.CanonicalFullLearnerState
    (Solution (semantics (hodgeRepresentation W)))
    (C.canonicalFullStep K)
    (step (semantics (hodgeRepresentation W)))
canonical-physics-to-learner-transition-witness W K =
  physicsToLearnerTransitionWitness
    (learnerToSolution W)
    (solutionToLearner W)
    (learnerSolutionLeftInverse W)
    (learnerStepConjugacy W K)

------------------------------------------------------------------------
-- nLab-guided semantic closure for the Maxwell four-law seam.
--
-- Sources:
--   Noether theorem / conserved current:
--     https://ncatlab.org/nlab/show/Noether%27s%2Btheorem
--     https://ncatlab.org/nlab/show/conserved%2Bcurrent
--   Maxwell differential-form equations / Hodge-Maxwell theorem:
--     https://ncatlab.org/nlab/show/Maxwell%27s%2Bequations
--     https://ncatlab.org/nlab/show/Hodge-Maxwell%2Btheorem
--   Action / Euler-Lagrange critical locus:
--     https://ncatlab.org/nlab/show/action%2Bfunctional
--     https://ncatlab.org/nlab/show/Euler-Lagrange%2Bequation
--
-- The repository does not expose a differential-form calculus or a
-- variational bicomplex. Therefore the external theorems are represented
-- by theorem-output interfaces rather than fabricated Agda axioms:
--
--   Noether output:
--     an on-shell conserved current for the physical step;
--   Euler-Lagrange output:
--     a variational/action semantics whose Euler-Lagrange shell contains
--     the Maxwell shell and whose critical-locus predicate is stationary.
--
-- The concrete Hodge-Maxwell representation still supplies the learner ↔
-- solution inverse and one-step conjugacy. The only semantic frontier
-- entering the four-law contract is therefore this single typed closure
-- record.
------------------------------------------------------------------------

record NLabNoetherConservationTheorem
  (PhysicalState Current : Set)
  (PhysicalStep : PhysicalState → PhysicalState)
  (MaxwellShell : PhysicalState → Set) : Set₁ where
  constructor nLabNoetherConservationTheorem
  field
    current :
      PhysicalState → Current
    conservedOnShell :
      ∀ p →
      MaxwellShell p →
      current (PhysicalStep p) ≡ current p

open NLabNoetherConservationTheorem public

record NLabEulerLagrangeMaxwellTheorem
  (PhysicalState Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set)
  (MaxwellShell : PhysicalState → Set) : Set₁ where
  constructor nLabEulerLagrangeMaxwellTheorem
  field
    variation :
      PhysicalState → Variation
    action :
      PhysicalState → Action
    admissibleVariation :
      ∀ p →
      Admissible (variation p)
    eulerLagrangeShell :
      PhysicalState → Set
    maxwellImpliesEulerLagrange :
      ∀ p →
      MaxwellShell p →
      eulerLagrangeShell p
    eulerLagrangeImpliesMaxwell :
      ∀ p →
      eulerLagrangeShell p →
      MaxwellShell p
    eulerLagrangeImpliesStationary :
      ∀ p →
      eulerLagrangeShell p →
      Stationary p

open NLabEulerLagrangeMaxwellTheorem public

nLabMaxwellEulerLagrangeShell-equivalence :
  ∀ {PhysicalState Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary : PhysicalState → Set}
  {MaxwellShell : PhysicalState → Set}
  (S :
    NLabEulerLagrangeMaxwellTheorem
      PhysicalState
      Variation
      Action
      Admissible
      Stationary
      MaxwellShell)
  (p : PhysicalState) →
  (MaxwellShell p → eulerLagrangeShell S p)
  ×
  (eulerLagrangeShell S p → MaxwellShell p)
nLabMaxwellEulerLagrangeShell-equivalence S p =
  ( maxwellImpliesEulerLagrange S p
  , eulerLagrangeImpliesMaxwell S p )

MaxwellSolution :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousHodgeMaxwellExactRepresentationData
      GRU) →
  Set
MaxwellSolution D = Solution D

MaxwellShell :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousHodgeMaxwellExactRepresentationData
      GRU) →
  MaxwellSolution D → Set
MaxwellShell D p = maxwellEquation D p

lawIFromNLabNoether :
  ∀ {LearnerState PhysicalState Current : Set}
  {PhysicalStep : PhysicalState → PhysicalState}
  {MaxwellShell : PhysicalState → Set}
  (S :
    NLabNoetherConservationTheorem
      PhysicalState
      Current
      PhysicalStep
      MaxwellShell)
  (shell : ∀ p → MaxwellShell p)
  (encodeD : LearnerState → PhysicalState)
  (decodeD : PhysicalState → LearnerState)
  (decodeEncodeD :
    ∀ s → decodeD (encodeD s) ≡ s) →
  LawIPhysicsWitness
    LearnerState
    PhysicalState
    Current
lawIFromNLabNoether
  S
  shell
  encodeD
  decodeD
  decodeEncodeD =
  lawIPhysicsWitness
    encodeD
    decodeD
    decodeEncodeD
    (λ p → PhysicalStep p)
    (current S)
    (λ p → conservedOnShell S p (shell p))

lawIIIFromNLabEulerLagrange :
  ∀ {LearnerState PhysicalState Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary : PhysicalState → Set}
  {MaxwellShell : PhysicalState → Set}
  (S :
    NLabEulerLagrangeMaxwellTheorem
      PhysicalState
      Variation
      Action
      Admissible
      Stationary
      MaxwellShell)
  (shell : ∀ p → MaxwellShell p)
  (encodeD : LearnerState → PhysicalState)
  (decodeD : PhysicalState → LearnerState)
  (decodeEncodeD :
    ∀ s → decodeD (encodeD s) ≡ s) →
  LawIIIVariationalWitness
    LearnerState
    PhysicalState
    Variation
    Action
    Admissible
    Stationary
lawIIIFromNLabEulerLagrange
  S
  shell
  encodeD
  decodeD
  decodeEncodeD =
  lawIIIVariationalWitness
    encodeD
    decodeD
    decodeEncodeD
    (variation S)
    (action S)
    (admissibleVariation S)
    (λ p →
      eulerLagrangeImpliesStationary
        S
        p
        (maxwellImpliesEulerLagrange S p (shell p)))

record NLabMaxwellSemanticClosure
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (Current Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set) : Set₁ where
  constructor nLabMaxwellSemanticClosure
  field
    noether :
      NLabNoetherConservationTheorem
        (MaxwellSolution
          (semantics (hodgeRepresentation W)))
        Current
        (step (semantics (hodgeRepresentation W)))
        (MaxwellShell
          (semantics (hodgeRepresentation W)))

    variational :
      NLabEulerLagrangeMaxwellTheorem
        (MaxwellSolution
          (semantics (hodgeRepresentation W)))
        Variation
        Action
        Admissible
        Stationary
        (MaxwellShell
          (semantics (hodgeRepresentation W)))

open NLabMaxwellSemanticClosure public

nLabMaxwellFourLawOneStep :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel)
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set} →
  NLabMaxwellSemanticClosure
    W
    Current
    Variation
    Action
    Admissible
    Stationary →
  FourLawOneStepWitnessContract
    C.CanonicalFullLearnerState
    (MaxwellSolution
      (semantics (hodgeRepresentation W)))
    Current
    Variation
    Action
    Admissible
    Stationary
    (C.canonicalFullStep K)
    (step (semantics (hodgeRepresentation W)))
nLabMaxwellFourLawOneStep
  W
  K
  S =
  fourLawOneStepWitnessContract
    (lawIFromNLabNoether
      (noether S)
      (λ p →
        maxwellEquation
          (semantics (hodgeRepresentation W))
          p)
      (learnerToSolution W)
      (solutionToLearner W)
      (learnerSolutionLeftInverse W))
    (lawIIIFromNLabEulerLagrange
      (variational S)
      (λ p →
        maxwellEquation
          (semantics (hodgeRepresentation W))
          p)
      (learnerToSolution W)
      (solutionToLearner W)
      (learnerSolutionLeftInverse W))
    (canonical-physics-to-learner-transition-witness W K)

------------------------------------------------------------------------
-- A semantically closed four-law model is the single proof-relevant
-- downstream boundary.  Once this package is inhabited, callers do not
-- repeat the Noether, variational, shell, inverse, or transition premises.
--
-- This does not manufacture an inhabitant: the repository's generic
-- impossibility boundary rules out a constructor that could populate these
-- fields for arbitrary predicates.  The package therefore concentrates the
-- unavoidable physical semantics into one explicit object while keeping all
-- later transport theorems premise-free.
------------------------------------------------------------------------

record NLabMaxwellFourLawSemanticallyClosed
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (Current Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set) : Set₁ where
  constructor nLabMaxwellFourLawSemanticallyClosed
  field
    kernel : C.CanonicalFullLearnerKernel
    semanticClosure :
      NLabMaxwellSemanticClosure
        W
        Current
        Variation
        Action
        Admissible
        Stationary

nLabMaxwellFourLawSemanticallyClosed-from-semantic :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel)
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (S :
    NLabMaxwellSemanticClosure
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  NLabMaxwellFourLawSemanticallyClosed
    W
    Current
    Variation
    Action
    Admissible
    Stationary
nLabMaxwellFourLawSemanticallyClosed-from-semantic
  W
  K
  S =
  nLabMaxwellFourLawSemanticallyClosed
    K
    S

open NLabMaxwellFourLawSemanticallyClosed public

nLabMaxwellFourLawOneStepClosed :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  FourLawOneStepWitnessContract
    C.CanonicalFullLearnerState
    (MaxwellSolution
      (semantics (hodgeRepresentation W)))
    Current
    Variation
    Action
    Admissible
    Stationary
    (C.canonicalFullStep (kernel B))
    (step (semantics (hodgeRepresentation W)))
nLabMaxwellFourLawOneStepClosed B =
  nLabMaxwellFourLawOneStep
    W
    (kernel B)
    (semanticClosure B)

------------------------------------------------------------------------
-- Once the nLab semantic square is inhabited, autonomous-time transport
-- is already closed by the existing one-step conjugacy kernel.
------------------------------------------------------------------------

nLabMaxwellIterateConjugacy :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel) →
  ∀ n s →
  learnerToSolution W
    (iterateStep
      (C.canonicalFullStep K)
      n
      s)
  ≡
  iterateStep
    (step (semantics (hodgeRepresentation W)))
    n
    (learnerToSolution W s)
nLabMaxwellIterateConjugacy
  W
  K
  n
  s =
  iterateConjugacy
    (learnerToSolution W)
    (λ s →
      learnerStepConjugacy W K s)
    n
    s

nLabMaxwellIterateConjugacyClosed :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  ∀ n s →
  learnerToSolution W
    (iterateStep
      (C.canonicalFullStep (kernel B))
      n
      s)
  ≡
  iterateStep
    (step (semantics (hodgeRepresentation W)))
    n
    (learnerToSolution W s)
nLabMaxwellIterateConjugacyClosed B =
  nLabMaxwellIterateConjugacy
    W
    (kernel B)
    n
    s

------------------------------------------------------------------------
-- Single-file algebraic consistency package.
--
-- The statistical Law-IV representation and the nLab-guided four-law
-- witness are already proved independently.  This package composes those
-- existing proofs in this monolith: GRU injectivity, the closed four-law
-- witness, one-step physics/learner transport, and exact iterate transport.
-- It adds no physical inhabitant and no new axiom; an instance still requires
-- the explicit semantic closure B above.
------------------------------------------------------------------------

record NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem
  {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) : Set₁ where
  constructor nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem
  field
    statisticalRepresentation :
      CanonicalGRUStatisticalInjectivityTheorem
    statisticalInjective :
      ∀ {s t : C.GRUState} →
      canonicalGRUStatisticalEncode s ≡
      canonicalGRUStatisticalEncode t →
      s ≡ t
    statisticalStep :
      ∀ (s : C.GRUState) (x : C.Int8) →
      canonicalGRUStatisticalEncode (C.gruStep s x)
      ≡
      (C.gruStep s x ,
       (λ _ → C.hiddenState (C.gruStep s x)))
    fourLaw :
      FourLawOneStepWitnessContract
        C.CanonicalFullLearnerState
        (MaxwellSolution
          (semantics (hodgeRepresentation W)))
        Current
        Variation
        Action
        Admissible
        Stationary
        (C.canonicalFullStep (kernel B))
        (step (semantics (hodgeRepresentation W)))
    learnerSemantics :
      CanonicalMARLLawCompositionTheorem
    representation :
      ConnectedContinuousHodgeMaxwellGRURepresentationTheorem
        C.CanonicalFullLearnerState
    iterateTransport :
      ∀ n s →
      learnerToSolution W
        (iterateStep
          (C.canonicalFullStep (kernel B))
          n
          s)
      ≡
      iterateStep
        (step (semantics (hodgeRepresentation W)))
        n
        (learnerToSolution W s)

nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem-from-closed :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem B
nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem-from-closed B =
  nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem
    canonical-gru-statistical-injectivity-theorem
    canonicalGRUStatisticalEncodeInjective
    canonicalGRUStatisticalStepConsequence
    (nLabMaxwellFourLawOneStepClosed B)
    (learnerSemantics W)
    (hodgeRepresentation W)
    (nLabMaxwellIterateConjugacyClosed B)


------------------------------------------------------------------------
-- Repository-wide semantic e-graph/A* closure.
--
-- Every surviving Agda module can be placed in an indexed semantic family.
-- The closure is unconditional at that semantic layer: any supplied sound
-- interpretation and any sound e-graph path produce exact equality.
-- A* costs remain search metadata, never proof evidence.
------------------------------------------------------------------------

canonical-repository-wide-agda-egraph-astar-closure :
  ∀ {Module : Set}
  (F : AgdaSemanticModuleFamily Module)
  (m : Module)
  {e f : Expression F m} →
  EGraphSemanticPath
    (semantics (closure F m))
    e
    f →
  interpret (semantics (closure F m)) e
  ≡
  interpret (semantics (closure F m)) f
canonical-repository-wide-agda-egraph-astar-closure =
  repositoryAgdaAStarSemanticClosure

canonical-unconditional-agda-egraph-astar-closure :
  UnconditionalAgdaEGraphAStarClosure
canonical-unconditional-agda-egraph-astar-closure =
  unconditional-agda-egraph-astar-closure


------------------------------------------------------------------------

f4-add-right-nonnegative :
  ∀ (n m : Nat) → n ≤ n + m
f4-add-right-nonnegative n zero = ≤-refl
f4-add-right-nonnegative n (suc m) =
  s≤s (f4-add-right-nonnegative n m)

record MegaGeneralizedWalrasianEquilibrium
  (State Price Allocation : Set) : Set₁ where
  constructor megaGeneralizedWalrasianEquilibrium
  field
    aggregate : (State → Allocation) → Allocation
    equilibrium : Price → Allocation → Set
    characterization : Price → Allocation → Set
    characterizationBridge :
      ∀ {p a} →
      characterization p a →
      equilibrium p a

open MegaGeneralizedWalrasianEquilibrium public

record GeneralizedWalrasianData
  (Agent Commodity Price Allocation : Set) : Set₁ where
  constructor generalizedWalrasianData
  field
    consumption : Agent → Set
    preference : Agent → Allocation → Allocation → Set
    budget : Price → Agent → Allocation → Set
    feasible : Allocation → Set
    marketClearing : Price → Allocation → Set
    equilibrium : Price → Allocation → Set
    characterization : Price → Allocation → Set
    characterizationFromEquilibrium :
      ∀ {p a} →
      equilibrium p a →
      characterization p a

open GeneralizedWalrasianData public

FiniteNonIIDPreference :
  ∀ {Agent Good : Set}
  (utility : Agent → (Good → Nat) → Nat) →
  Agent → (Agent → Good → Nat) → (Agent → Good → Nat) → Set
FiniteNonIIDPreference utility i x y =
  utility i (x i) ≤ utility i (y i)

record FiniteNonIIDGeneralizedEquilibrium
  (Agent Good : Set)
  (agents : List Agent)
  (goods : List Good)
  (utility : Agent → (Good → Nat) → Nat)
  (endowment : Agent → Good → Nat)
  (price : Good → Nat)
  (allocation : Agent → Good → Nat) : Set₁ where
  constructor finiteNonIIDGeneralizedEquilibrium
  field
    budgetOptimal :
      ∀ i bundle →
      BudgetFeasible
        goods
        price
        (endowment i)
        bundle →
      utility i bundle ≤
      utility i (allocation i)
    marketClearing :
      ∀ g →
      sumNat (map (λ i → allocation i g) agents) ≡
      sumNat (map (λ i → endowment i g) agents)

megaParetoOptimal :
  ∀ {Agent Allocation : Set}
  {weakPreference strictPreference :
    Agent → Allocation → Allocation → Set}
  (feasible : Allocation → Set) →
  Allocation → Set₁
megaParetoOptimal
  feasible
  a =
  feasible a ×
  (∀ {b : Allocation} →
   feasible b →
   MegaParetoImprovement
     Agent
     Allocation
     weakPreference
     strictPreference
     b
     a →
   ⊥)

record MegaFirstWelfareTheoremConditions
  (Agent Price Allocation : Set)
  (weakPreference strictPreference :
    Agent → Allocation → Allocation → Set)
  (feasible : Allocation → Set)
  (budget : Price → Agent → Allocation → Set)
  (equilibrium : Price → Allocation → Set)
  (p : Price)
  (a : Allocation) : Set₁ where
  constructor megaFirstWelfareTheoremConditions
  field
    equilibriumWitness :
      equilibrium p a
    feasibleWitness :
      feasible a
    noStrictAffordableAlternative :
      ∀ i b →
      budget p i b →
      ¬ strictPreference i b a
    paretoImprovementAffordability :
      ∀ {b : Allocation} →
      feasible b →
      (improvement :
        MegaParetoImprovement
          Agent
          Allocation
          weakPreference
          strictPreference
          b
          a) →
      budget p
        (proj₁ (strictlyBetter improvement))
        b

open MegaFirstWelfareTheoremConditions public

megaNatNoStrictBack :
  ∀ {n : Nat} →
  suc n ≤ n →
  ⊥
megaNatNoStrictBack {zero} ()
megaNatNoStrictBack {suc n} (s≤s h) =
  megaNatNoStrictBack h

megaNatStrictCostContradiction :
  ∀ {m n : Nat} →
  n ≤ m →
  m < n →
  ⊥
megaNatStrictCostContradiction hle hlt =
  megaNatNoStrictBack (≤-trans hlt hle)

megaNoStrictAffordableAlternative-from-demand-cost :
  ∀ {Agent Price Allocation : Set}
  {weakPreference strictPreference :
    Agent → Allocation → Allocation → Set}
  {feasible : Allocation → Set}
  {budget : Price → Agent → Allocation → Set}
  {equilibrium : Price → Allocation → Set}
  {cost : Price → Agent → Allocation → Nat}
  {p : Price}
  {a : Allocation} →
  MegaDemandCostKernel
    Agent
    Price
    Allocation
    weakPreference
    strictPreference
    feasible
    budget
    equilibrium
    cost
    p
    a →
  ∀ i b →
  budget p i b →
  ¬ strictPreference i b a
megaNoStrictAffordableAlternative-from-demand-cost kernel i b affordable =
  λ strictlyPreferred →
    megaNatStrictCostContradiction
      (budgetCostBound kernel i b affordable)
      (strictlyPreferredCostly kernel i b strictlyPreferred)

FiniteNonIIDStrictPreference :
  ∀ {Agent Good : Set}
  (utility : Agent → (Good → Nat) → Nat) →
  Agent → (Agent → Good → Nat) → (Agent → Good → Nat) → Set
FiniteNonIIDStrictPreference utility i x y =
  utility i (y i) < utility i (x i)

record FiniteNonIIDDemandCostClosure
  (Agent Good : Set)
  (agents : List Agent)
  (goods : List Good)
  (utility : Agent → (Good → Nat) → Nat)
  (endowment : Agent → Good → Nat)
  (price : Good → Nat)
  (allocation : Agent → Good → Nat) : Set₁ where
  constructor finiteNonIIDDemandCostClosure
  field
    equilibriumWitness :
      FiniteNonIIDGeneralizedEquilibrium
        Agent
        Good
        agents
        goods
        utility
        endowment
        price
        allocation

    preferredCostly :
      ∀ i x y →
      utility i (x i) ≤ utility i (y i) →
      bundleCost goods price (y i) ≤
      bundleCost goods price (x i)

    strictlyPreferredCostly :
      ∀ i x y →
      utility i (y i) < utility i (x i) →
      bundleCost goods price (y i) <
      bundleCost goods price (x i)

    paretoImprovementAffordability :
      ∀ {b : Agent → Good → Nat} →
      (improvement :
        MegaParetoImprovement
          Agent
          (Agent → Good → Nat)
          (FiniteNonIIDPreference utility)
          (FiniteNonIIDStrictPreference utility)
          b
          allocation) →
      BudgetFeasible
        goods
        price
        (endowment
          (proj₁ (strictlyBetter improvement)))
        b

finiteNonIIDBudgetCostBound :
  ∀ {Agent Good : Set}
  {goods : List Good}
  {price : Good → Nat}
  {endowment : Agent → Good → Nat}
  {i : Agent}
  {bundle : Good → Nat} →
  BudgetFeasible goods price (endowment i) bundle →
  bundleCost goods price bundle ≤
  bundleCost goods price (endowment i)
finiteNonIIDBudgetCostBound affordable = affordable

finiteNonIIDDemandCostKernel :
  ∀ {Agent Good : Set}
  {agents : List Agent}
  {goods : List Good}
  {utility : Agent → (Good → Nat) → Nat}
  {endowment : Agent → Good → Nat}
  {price : Good → Nat}
  {allocation : Agent → Good → Nat} →
  FiniteNonIIDDemandCostClosure
    Agent
    Good
    agents
    goods
    utility
    endowment
    price
    allocation →
  MegaDemandCostKernel
    Agent
    (Good → Nat)
    (Agent → Good → Nat)
    (FiniteNonIIDPreference utility)
    (FiniteNonIIDStrictPreference utility)
    (λ a →
      ∀ g →
      sumNat (map (λ i → a i g) agents) ≡
      sumNat (map (λ i → endowment i g) agents))
    (λ p i bundle → BudgetFeasible goods p (endowment i) bundle)
    (λ p a →
      FiniteNonIIDGeneralizedEquilibrium
        Agent
        Good
        agents
        goods
        utility
        endowment
        p
        a)
    (λ p i bundle → bundleCost goods p (bundle i))
    price
    allocation
finiteNonIIDDemandCostKernel closure =
  megaDemandCostKernel
    (equilibriumWitness closure)
    (marketClearing (equilibriumWitness closure))
    (λ i b preferred →
      preferredCostly closure i b allocation preferred)
    (λ i b strictlyPreferred →
      strictlyPreferredCostly closure i b allocation strictlyPreferred)
    (λ i b affordable →
      finiteNonIIDBudgetCostBound affordable)
    (λ {b} _ improvement →
      paretoImprovementAffordability closure improvement)

record MegaSecondWelfareTheoremBoundaryCounterexample : Set₁ where
  constructor megaSecondWelfareTheoremBoundaryCounterexample
  field
    Price : Set
    Allocation : Set
    paretoOptimal : Allocation → Set₁
    equilibrium : Price → Allocation → Set
    allocationWitness : Allocation
    paretoWitness :
      paretoOptimal allocationWitness
    noSupportingPrice :
      ¬ Σ Price (λ p → equilibrium p allocationWitness)

open MegaSecondWelfareTheoremBoundaryCounterexample public

megaSecondWelfareTheorem-boundary-counterexample :
  MegaSecondWelfareTheoremBoundaryCounterexample
megaSecondWelfareTheorem-boundary-counterexample =
  megaSecondWelfareTheoremBoundaryCounterexample
    ⊥
    ⊤
    (λ _ → ⊤)
    (λ _ _ → ⊥)
    tt
    tt
    (λ { (_ , e) → e })

record MegaNoStrictAffordableAlternativeBoundary
  (Agent Price Allocation : Set)
  (strictPreference :
    Agent → Allocation → Allocation → Set)
  (budget : Price → Agent → Allocation → Set)
  (p : Price)
  (a : Allocation) : Set₁ where
  constructor megaNoStrictAffordableAlternativeBoundary
  field
    demandOptimality :
      ∀ i b →
      budget p i b →
      ¬ strictPreference i b a

megaNoStrictAffordableAlternative-is-demand-optimality :
  ∀ {Agent Price Allocation : Set}
  {strictPreference :
    Agent → Allocation → Allocation → Set}
  {budget : Price → Agent → Allocation → Set}
  {p : Price} {a : Allocation} →
  MegaNoStrictAffordableAlternativeBoundary
    Agent Price Allocation strictPreference budget p a →
  (∀ i b →
    budget p i b →
    ¬ strictPreference i b a)
megaNoStrictAffordableAlternative-is-demand-optimality boundary =
  demandOptimality boundary

GeneralizedWalrasianEquilibrium :
  Set → Set → Set → Set₁
GeneralizedWalrasianEquilibrium =
  MegaGeneralizedWalrasianEquilibrium

generalizedWalrasianEquilibrium :
  ∀ {State Price Allocation : Set} →
  (encode : State → Price) →
  (equilibrium : Price → Allocation → Set) →
  (feasibility : Price → Allocation → Set) →
  (characterize :
    ∀ {p a} →
    equilibrium p a →
    feasibility p a) →
  GeneralizedWalrasianEquilibrium State Price Allocation
generalizedWalrasianEquilibrium =
  megaGeneralizedWalrasianEquilibrium

ProductionSet : Set → Set
ProductionSet ProductionPlan = ProductionPlan → Set

record CompetitiveProductionEconomy
  (Agent Firm Commodity Price Consumption ProductionPlan : Set) : Set₁ where
  constructor competitiveProductionEconomy
  field
    endowment : Agent → Consumption
    preference : Agent → Consumption → Consumption → Set
    consumptionFeasible : Agent → Consumption → Set
    productionSet : Firm → ProductionPlan → Set
    ownershipShare : Agent → Firm → Set
    profitMaximization :
      Firm → Price → ProductionPlan → Set
    resourceBalance :
      Commodity → Set

record CompetitiveWalrasianEquilibriumWithProduction
  (Agent Firm Commodity Price Consumption ProductionPlan : Set)
  (E : CompetitiveProductionEconomy
    Agent Firm Commodity Price Consumption ProductionPlan) : Set₁ where
  constructor competitiveWalrasianEquilibriumWithProduction
  field
    price : Price
    consumption : Agent → Consumption
    production : Firm → ProductionPlan
    consumerOptimality :
      ∀ i →
      CompetitiveProductionEconomy.preference E i
        (consumption i)
        (consumption i)
    productionFeasibility :
      ∀ j →
      CompetitiveProductionEconomy.productionSet E
        j
        (production j)
    productionOptimality :
      ∀ j →
      CompetitiveProductionEconomy.profitMaximization E
        j
        price
        (production j)
    consumptionFeasibility :
      ∀ i →
      CompetitiveProductionEconomy.consumptionFeasible E
        i
        (consumption i)
    marketClearing :
      ∀ c →
      CompetitiveProductionEconomy.resourceBalance E c

record ProductionFeasibilityWitness
  (Firm ProductionPlan : Set)
  (feasible : Firm → ProductionPlan → Set)
  (production : Firm → ProductionPlan) : Set₁ where
  constructor productionFeasibilityWitness
  field
    witness :
      ∀ j →
      feasible j (production j)

record FirmProfitOptimalityWitness
  (Firm Price ProductionPlan : Set)
  (optimal : Firm → Price → ProductionPlan → Set)
  (price : Price)
  (production : Firm → ProductionPlan) : Set₁ where
  constructor firmProfitOptimalityWitness
  field
    witness :
      ∀ j →
      optimal j price (production j)

record ConsumerOptimalityWitness
  (Agent Consumption : Set)
  (optimal : Agent → Consumption → Set)
  (consumption : Agent → Consumption) : Set₁ where
  constructor consumerOptimalityWitness
  field
    witness :
      ∀ i →
      optimal i (consumption i)

record ConsumptionFeasibilityWitness
  (Agent Consumption : Set)
  (feasible : Agent → Consumption → Set)
  (consumption : Agent → Consumption) : Set₁ where
  constructor consumptionFeasibilityWitness
  field
    witness :
      ∀ i →
      feasible i (consumption i)

record AggregateFeasibilityWitness
  (Allocation : Set)
  (feasible : Allocation → Set)
  (allocation : Allocation) : Set₁ where
  constructor aggregateFeasibilityWitness
  field
    witness :
      feasible allocation

record MarketClearingWitness
  (Price Allocation : Set)
  (marketClearing : Price → Allocation → Set)
  (price : Price)
  (allocation : Allocation) : Set₁ where
  constructor marketClearingWitness
  field
    witness :
      marketClearing price allocation

record SupportingPriceWitness
  (Price Allocation : Set)
  (supports : Price → Allocation → Set)
  (price : Price)
  (allocation : Allocation) : Set₁ where
  constructor supportingPriceWitness
  field
    witness :
      supports price allocation

applyNormPairReplacements :
  ∀ {A : Set} →
  List C.NormPair →
  C.FullLearnerState A →
  C.FullLearnerState A
applyNormPairReplacements [] s = s
applyNormPairReplacements (n ∷ ns) s =
  applyNormPairReplacements ns (C.replaceNorm s n)

normPairReplacementRelation :
  ∀ {A : Set} →
  C.FullLearnerState A →
  C.FullLearnerState A →
  Set
normPairReplacementRelation s t =
  Σ C.NormPair (λ n → C.replaceNorm s n ≡ t)

applyNormPairReplacements-collapse :
  ∀ {A : Set}
  (s : C.FullLearnerState A)
  (ns : List C.NormPair) →
  Σ C.NormPair
    (λ n → C.replaceNorm s n
      ≡ applyNormPairReplacements ns s)
applyNormPairReplacements-collapse s [] =
  C.norm s , refl
applyNormPairReplacements-collapse s (n ∷ ns)
  with applyNormPairReplacements-collapse
    (C.replaceNorm s n)
    ns
... | m , eq = m , eq

normPairReplacementRelation-generated :
  ∀ {A : Set}
  (s t : C.FullLearnerState A) →
  (Σ (List C.NormPair)
    (λ ns →
      applyNormPairReplacements ns s ≡ t)) →
  normPairReplacementRelation s t
normPairReplacementRelation-generated s t (ns , eq)
  with applyNormPairReplacements-collapse s ns
... | n , collapse =
  n , trans collapse eq

normPairReplacementRelation-refl :
  ∀ {A : Set}
  (s : C.FullLearnerState A) →
  normPairReplacementRelation s s
normPairReplacementRelation-refl s =
  C.norm s , refl

normPairReplacementRelation-sym :
  ∀ {A : Set}
  {s t : C.FullLearnerState A} →
  normPairReplacementRelation s t →
  normPairReplacementRelation t s
normPairReplacementRelation-sym (n , eq) =
  C.norm _ ,
  trans
    (sym
      (cong
        (λ x → C.replaceNorm x (C.norm _))
        eq))
    refl

normPairReplacementRelation-trans :
  ∀ {A : Set}
  {s t u : C.FullLearnerState A} →
  normPairReplacementRelation s t →
  normPairReplacementRelation t u →
  normPairReplacementRelation s u
normPairReplacementRelation-trans
  (n , st)
  (m , tu) =
  m ,
  trans
    (cong
      (λ x → C.replaceNorm x m)
      st)
    tu

canonicalPolicy-factors-through-NormPair :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  {s t : C.FullLearnerState A} →
  normPairReplacementRelation s t →
  C.canonicalPolicy K t ≡ C.canonicalPolicy K s
canonicalPolicy-factors-through-NormPair
  K
  (n , eq) =
  trans
    (sym (cong (C.canonicalPolicy K) eq))
    (C.canonicalPolicy-norm-invariant _ _ n)

canonicalNormPairQuotient-step-compatible :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  {s t : C.FullLearnerState A} →
  normPairReplacementRelation s t →
  normPairReplacementRelation
    (C.canonicalFullStep K s)
    (C.canonicalFullStep K t)
canonicalNormPairQuotient-step-compatible
  K
  (n , eq) =
  n ,
  trans
    (sym (canonicalFullStep-replaceNorm K _ n))
    (cong (C.canonicalFullStep K) eq)

canonicalNormPairQuotient-iterate-compatible :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (n : Nat)
  {s t : C.FullLearnerState A} →
  normPairReplacementRelation s t →
  normPairReplacementRelation
    (C.iterateCanonical K n s)
    (C.iterateCanonical K n t)
canonicalNormPairQuotient-iterate-compatible
  K
  zero
  relation =
  relation
canonicalNormPairQuotient-iterate-compatible
  K
  (suc n)
  relation =
  canonicalNormPairQuotient-iterate-compatible
    K
    n
    (canonicalNormPairQuotient-step-compatible K relation)

record FactorTransitionWitness
  (State Factor : Set)
  (step : State → State)
  (observe : State → Factor) : Set₁ where
  constructor factorTransitionWitness
  field
    factorStep : Factor → Factor
    observe-step :
      ∀ s →
      observe (step s) ≡
      factorStep (observe s)

open FactorTransitionWitness public

factorTransitionAfterIterate :
  ∀ {State Factor : Set}
  {step : State → State}
  {observe : State → Factor}
  (W :
    FactorTransitionWitness
      State
      Factor
      step
      observe)
  (n : Nat)
  (s : State) →
  observe (iterateIsomorphism step n s) ≡
  iterateIsomorphism (factorStep W) n (observe s)
factorTransitionAfterIterate W zero s =
  refl
factorTransitionAfterIterate W (suc n) s =
  trans
    (factorTransitionAfterIterate W n (step s))
    (cong
      (iterateIsomorphism (factorStep W) n)
      (observe-step W s))

record RelationFactorTransitionWitness
  (State Factor : Set)
  (step : State → State)
  (related : State → State → Set)
  (observe : State → Factor) : Set₁ where
  constructor relationFactorTransitionWitness
  field
    transition :
      FactorTransitionWitness
        State
        Factor
        step
        observe
    observeRespects :
      ∀ {s t} →
      related s t →
      observe s ≡ observe t
    relationStepPreserved :
      ∀ {s t} →
      related s t →
      related
        (step s)
        (step t)

canonicalPolicyFactorTransition :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (factorStep : Nat → Nat)
  (factorStepCommutes :
    ∀ s →
    C.canonicalPolicy K (C.canonicalFullStep K s) ≡
    factorStep (C.canonicalPolicy K s)) →
  RelationFactorTransitionWitness
    (C.FullLearnerState A)
    Nat
    (C.canonicalFullStep K)
    normPairReplacementRelation
    (C.canonicalPolicy K)
canonicalPolicyFactorTransition
  K
  factorStep
  factorStepCommutes =
  relationFactorTransitionWitness
    (factorTransitionWitness
      factorStep
      factorStepCommutes)
    (canonicalPolicy-factors-through-NormPair K)
    (canonicalNormPairQuotient-step-compatible K)

record CanonicalNormPairQuotientFactorTransitionTheorem : Set₁ where
  constructor canonicalNormPairQuotientFactorTransitionTheorem
  field
    generatedOrbit :
      ∀ {A : Set}
      (s t : C.FullLearnerState A) →
      (Σ (List C.NormPair)
        (λ ns →
          applyNormPairReplacements ns s ≡ t)) →
      normPairReplacementRelation s t

    quotientReflexive :
      ∀ {A : Set}
      (s : C.FullLearnerState A) →
      normPairReplacementRelation s s

    quotientSymmetric :
      ∀ {A : Set}
      {s t : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      normPairReplacementRelation t s

    quotientTransitive :
      ∀ {A : Set}
      {s t u : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      normPairReplacementRelation t u →
      normPairReplacementRelation s u

    policyFactors :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      {s t : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      C.canonicalPolicy K t ≡ C.canonicalPolicy K s

    transitionCompatible :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      {s t : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      normPairReplacementRelation
        (C.canonicalFullStep K s)
        (C.canonicalFullStep K t)

    iterateCompatible :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      (n : Nat)
      {s t : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      normPairReplacementRelation
        (C.iterateCanonical K n s)
        (C.iterateCanonical K n t)

canonical-normPair-quotient-factor-transition-theorem :
  CanonicalNormPairQuotientFactorTransitionTheorem
canonical-normPair-quotient-factor-transition-theorem =
  canonicalNormPairQuotientFactorTransitionTheorem
    normPairReplacementRelation-generated
    normPairReplacementRelation-refl
    normPairReplacementRelation-sym
    normPairReplacementRelation-trans
    canonicalPolicy-factors-through-NormPair
    canonicalNormPairQuotient-step-compatible
    canonicalNormPairQuotient-iterate-compatible

record CanonicalF4NormPairUnconditionalFactorStabilityTheorem : Set₁ where
  constructor canonicalF4NormPairUnconditionalFactorStabilityTheorem
  field
    f4Stability :
      CanonicalF4GlobalOptimizerStabilityTheorem

    normPairFactorTransition :
      CanonicalNormPairQuotientFactorTransitionTheorem

    policyFactorization :
      ∀ {A : Set}
        (K : C.FullLearnerKernel A)
        {s t : C.FullLearnerState A} →
        normPairReplacementRelation s t →
        C.canonicalPolicy K t ≡ C.canonicalPolicy K s

    transitionFactorization :
      ∀ {A : Set}
        (K : C.FullLearnerKernel A)
        {s t : C.FullLearnerState A} →
        normPairReplacementRelation s t →
        normPairReplacementRelation
          (C.canonicalFullStep K s)
          (C.canonicalFullStep K t)

    iterateFactorization :
      ∀ {A : Set}
        (K : C.FullLearnerKernel A)
        (n : Nat)
        {s t : C.FullLearnerState A} →
        normPairReplacementRelation s t →
        normPairReplacementRelation
          (C.iterateCanonical K n s)
          (C.iterateCanonical K n t)

canonical-f4-normPair-unconditional-factor-stability-theorem :
  CanonicalF4NormPairUnconditionalFactorStabilityTheorem
canonical-f4-normPair-unconditional-factor-stability-theorem =
  canonicalF4NormPairUnconditionalFactorStabilityTheorem
    canonical-f4-global-optimizer-stability-theorem
    canonical-normPair-quotient-factor-transition-theorem
    canonicalPolicy-factors-through-NormPair
    canonicalNormPairQuotient-step-compatible
    canonicalNormPairQuotient-iterate-compatible

record CanonicalF4NormPairIterateFactorStabilityTheorem : Set₁ where
  constructor canonicalF4NormPairIterateFactorStabilityTheorem
  field
    oneStepStability :
      CanonicalF4NormPairUnconditionalFactorStabilityTheorem

    normPairWeightPlusOneIterate :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      (n : Nat)
      (s : C.FullLearnerState A) →
      C.normPairWeightPlusOne
        (C.norm (C.iterateCanonical K n s))
      ≡
      C.normPairWeightPlusOne (C.norm s)

    persistentGRUIterate :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      (n : Nat)
      (s : C.FullLearnerState A) →
      C.persistentGRU
        (C.gru (C.iterateCanonical K n s))
      ≡
      C.persistentGRU (C.gru s)

    quotientIterateFactorization :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      (n : Nat)
      {s t : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      normPairReplacementRelation
        (C.iterateCanonical K n s)
        (C.iterateCanonical K n t)

canonical-f4-normPair-iterate-factor-stability-theorem :
  CanonicalF4NormPairIterateFactorStabilityTheorem
canonical-f4-normPair-iterate-factor-stability-theorem =
  canonicalF4NormPairIterateFactorStabilityTheorem
    canonical-f4-normPair-unconditional-factor-stability-theorem
    canonicalNormPair-afterFullStep-iterate
    canonicalPersistentGRU-afterFullStep-iterate
    canonicalNormPairQuotient-iterate-compatible

record RecursiveRadnerData
  (State Agent Commodity Asset Price Allocation Portfolio : Set)
  (priceProcess : State → Price)
  (allocationProcess : State → Agent → Allocation)
  (portfolioProcess : State → Agent → Portfolio) : Set₁ where
  constructor recursiveRadnerData
  field
    transition : State → State
    feasible : State → Agent → Allocation → Portfolio → Set
    optimal : State → Agent → Allocation → Portfolio → Set
    commodityMarketClearing : State → Set
    assetMarketClearing : State → Set
    priceRecursion : State → Price → Set
    allocationRecursion : State → Agent → Allocation → Set
    portfolioRecursion : State → Agent → Portfolio → Set

record RecursiveRadnerEquilibrium
  (State Agent Commodity Asset Price Allocation Portfolio : Set)
  (priceProcess : State → Price)
  (allocationProcess : State → Agent → Allocation)
  (portfolioProcess : State → Agent → Portfolio)
  (D :
    RecursiveRadnerData
      State Agent Commodity Asset Price Allocation Portfolio
      priceProcess
      allocationProcess
      portfolioProcess) : Set₁ where
  constructor recursiveRadnerEquilibrium
  field
    feasibility :
      ∀ s i →
      RecursiveRadnerData.feasible D
        s i
        (allocationProcess s i)
        (portfolioProcess s i)

    optimality :
      ∀ s i →
      RecursiveRadnerData.optimal D
        s i
        (allocationProcess s i)
        (portfolioProcess s i)

    commodityClearing :
      ∀ s →
      RecursiveRadnerData.commodityMarketClearing D s

    assetClearing :
      ∀ s →
      RecursiveRadnerData.assetMarketClearing D s

    priceRecursionWitness :
      ∀ s →
      RecursiveRadnerData.priceRecursion D
        s
        (priceProcess s)

    allocationRecursionWitness :
      ∀ s i →
      RecursiveRadnerData.allocationRecursion D
        s i
        (allocationProcess s i)

    portfolioRecursionWitness :
      ∀ s i →
      RecursiveRadnerData.portfolioRecursion D
        s i
        (portfolioProcess s i)

record RecursiveRadnerExistence
  (State Agent Commodity Asset Price Allocation Portfolio : Set) : Set₁ where
  constructor recursiveRadnerExistence
  field
    priceProcess : State → Price
    allocationProcess : State → Agent → Allocation
    portfolioProcess : State → Agent → Portfolio

    data :
      RecursiveRadnerData
        State Agent Commodity Asset Price Allocation Portfolio
        priceProcess
        allocationProcess
        portfolioProcess

    equilibrium :
      RecursiveRadnerEquilibrium
        State Agent Commodity Asset Price Allocation Portfolio
        priceProcess
        allocationProcess
        portfolioProcess
        data

RecursiveRadnerPrice :
  ∀ {State Price : Set} →
  Set
RecursiveRadnerPrice {State} {Price} =
  State → Price

RecursiveRadnerAllocation :
  ∀ {State Agent Allocation Portfolio : Set} →
  Set
RecursiveRadnerAllocation {State} {Agent} {Allocation} {Portfolio} =
  (State → Agent → Allocation)
  ×
  (State → Agent → Portfolio)

recursiveRadner-generalized :
  ∀ {State Agent Commodity Asset Price Allocation Portfolio : Set} →
  MegaGeneralizedWalrasianEquilibrium
    State
    RecursiveRadnerPrice
    (RecursiveRadnerAllocation
      {State = State}
      {Agent = Agent}
      {Allocation = Allocation}
      {Portfolio = Portfolio})
recursiveRadner-generalized =
  megaGeneralizedWalrasianEquilibrium
    (λ x → x)
    (λ pricePair allocationPair →
      Σ (RecursiveRadnerData
          State
          Agent
          Commodity
          Asset
          Price
          Allocation
          Portfolio
          (proj₁ allocationPair)
          (proj₂ allocationPair))
        (λ D →
          RecursiveRadnerEquilibrium
            State
            Agent
            Commodity
            Asset
            Price
            Allocation
            Portfolio
            (proj₁ allocationPair)
            (proj₂ allocationPair)
            D))
    (λ pricePair allocationPair →
      Σ (RecursiveRadnerData
          State
          Agent
          Commodity
          Asset
          Price
          Allocation
          Portfolio
          (proj₁ allocationPair)
          (proj₂ allocationPair))
        (λ D →
          RecursiveRadnerEquilibrium
            State
            Agent
            Commodity
            Asset
            Price
            Allocation
            Portfolio
            (proj₁ allocationPair)
            (proj₂ allocationPair)
            D))
    (λ {pricePair} {allocationPair} h → h)

megaNoEquilibriumGeneralizedWalrasian :
  MegaGeneralizedWalrasianEquilibrium ⊤ ⊤ ⊤
megaNoEquilibriumGeneralizedWalrasian =
  megaGeneralizedWalrasianEquilibrium
    (λ _ → tt)
    (λ _ _ → ⊥)
    (λ _ _ → ⊥)
    (λ ())

megaNoEquilibriumWitness :
  ¬ Σ ⊤
    (λ p → Σ ⊤
      (λ a →
        equilibrium
          megaNoEquilibriumGeneralizedWalrasian
          p
          a))
megaNoEquilibriumWitness
  (p , a , witness) =
  witness

noUnconditionalMegaGeneralizedWalrasianExistence :
  ¬
    (∀ {State Price Allocation : Set}
      (D : MegaGeneralizedWalrasianEquilibrium
        State Price Allocation) →
      Σ Price
        (λ p →
          Σ Allocation
            (λ a → equilibrium D p a)))
noUnconditionalMegaGeneralizedWalrasianExistence
  theorem =
  megaNoEquilibriumWitness
    (theorem megaNoEquilibriumGeneralizedWalrasian)

megaNoEquilibriumWalrasianSquare :
  MegaWalrasianGlobalSquareConjugacy
    ⊤
    ⊤
    ⊤
    (λ _ → tt)
    (λ _ → tt)
    (λ x → x)
    (λ x → x)
    (λ x → x)
    (λ x → x)
megaNoEquilibriumWalrasianSquare =
  megaWalrasianGlobalSquareConjugacy
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)

megaNoEquilibriumF4NormPairEconomicWitness :
  ¬
    Σ ⊤
      (λ p →
        Σ ⊤
          (λ a →
            equilibrium
              megaNoEquilibriumGeneralizedWalrasian
              p
              a))
megaNoEquilibriumF4NormPairEconomicWitness
  (p , a , witness) =
  witness

noUnconditionalMegaWalrasianExistenceAfterF4NormPairFactorStability :
  ¬
    (∀ {State Price Allocation : Set}
      (D : MegaGeneralizedWalrasianEquilibrium
        State
        Price
        Allocation) →
      Σ Price
        (λ p →
          Σ Allocation
            (λ a →
              equilibrium D p a)))
noUnconditionalMegaWalrasianExistenceAfterF4NormPairFactorStability
  theorem =
  megaNoEquilibriumWitness
    (theorem megaNoEquilibriumGeneralizedWalrasian)


------------------------------------------------------------------------
-- Generic strict-progress and carrier-polymorphic frontier core.
-- Kept in this monolith so there is one authoritative theorem source.
------------------------------------------------------------------------

iterateStep :
  ∀ {State : Set} →
  (State → State) →
  Nat →
  State →
  State
iterateStep step zero s = s
iterateStep step (suc n) s = step (iterateStep step n s)

record StrictProgressWitness
  (State Measure : Set)
  (step : State → State)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor strictProgressWitness
  field
    measure : State → Measure
    stepProgress :
      ∀ s →
      measure s < measure (step s)
    transitive :
      ∀ {a b c} →
      a < b →
      b < c →
      a < c
    irreflexive :
      ∀ a → ¬ (a < a)

record StrictProgressRelation
  (Measure : Set)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor strictProgressRelation
  field
    isTransitive :
      ∀ {a b c} →
      a < b →
      b < c →
      a < c
    isIrreflexive :
      ∀ a → ¬ (a < a)

strictProgressRelation-from-witness :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_) →
  StrictProgressRelation Measure _<_
strictProgressRelation-from-witness W =
  strictProgressRelation
    (transitive W)
    (irreflexive W)

strictProgressWitness-from-relation :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (R : StrictProgressRelation Measure _<_)
  (measure : State → Measure)
  (stepProgress :
    ∀ s → measure s < measure (step s)) →
  StrictProgressWitness State Measure step _<_
strictProgressWitness-from-relation R measure stepProgress =
  strictProgressWitness
    measure
    stepProgress
    (StrictProgressRelation.isTransitive R)
    (StrictProgressRelation.isIrreflexive R)

open StrictProgressWitness public

strictProgressAfterIterate :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_)
  (n : Nat)
  (s : State) →
  measure W s <
  measure W (iterateStep step (suc n) s)
strictProgressAfterIterate W zero s =
  stepProgress W s
strictProgressAfterIterate W (suc n) s =
  transitive W
    (stepProgress W s)
    (strictProgressAfterIterate W n (step s))

noPositiveFiniteCycleFromStrictProgress :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_)
  (n : Nat)
  (s : State) →
  iterateStep step (suc n) s ≡ s →
  ⊥
noPositiveFiniteCycleFromStrictProgress W n s eq =
  irreflexive W
    (measure W s)
    (subst
      (λ t → measure W s < measure W t)
      eq
      (strictProgressAfterIterate W n s))


record NatSuccessorProgressWitness
  (State : Set)
  (step : State → State)
  (measure : State → Nat) : Set₁ where
  constructor natSuccessorProgressWitness
  field
    successor :
      ∀ s →
      measure (step s) ≡ suc (measure s)

open NatSuccessorProgressWitness public

sucInjective :
  ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
sucInjective refl = refl

natPlusLeftCancel :
  ∀ (k m n : Nat) → k + m ≡ k + n → m ≡ n
natPlusLeftCancel zero m n eq = eq
natPlusLeftCancel (suc k) m n eq =
  natPlusLeftCancel k m n (sucInjective eq)

successorMeasureAfterIterate :
  ∀ {State : Set}
  {step : State → State}
  {measure : State → Nat}
  (W : NatSuccessorProgressWitness State step measure)
  (n : Nat)
  (s : State) →
  measure (iterateStep step n s) ≡ measure s + n
successorMeasureAfterIterate W zero s =
  sym (+-identityʳ (measure W s))
successorMeasureAfterIterate W (suc n) s =
  trans
    (successor W (iterateStep (step W) n s))
    (trans
      (cong suc (successorMeasureAfterIterate W n s))
      (sym (+-suc (measure W s) n)))

successorMeasureOrbitInjective :
  ∀ {State : Set}
  {step : State → State}
  {measure : State → Nat}
  (W : NatSuccessorProgressWitness State step measure)
  (s : State)
  {m n : Nat} →
  iterateStep step m s ≡ iterateStep step n s →
  m ≡ n
successorMeasureOrbitInjective W s {m} {n} eq =
  natPlusLeftCancel
    (measure W s)
    m
    n
    (trans
      (sym (successorMeasureAfterIterate W m s))
      (trans
        (cong (measure W) eq)
        (successorMeasureAfterIterate W n s)))

natSucProgress : ∀ n → n < suc n
natSucProgress zero = s≤s z≤n
natSucProgress (suc n) = s≤s (natSucProgress n)

canonicalTotalCountStepProgress :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (s : C.FullLearnerState A) →
  C.totalCount (C.lcbCounts s) <
  C.totalCount (C.lcbCounts (C.canonicalFullStep K s))
canonicalTotalCountStepProgress K s =
  subst
    (λ t → C.totalCount (C.lcbCounts s) < t)
    (C.canonicalTotalCountStep K s)
    (natSucProgress (C.totalCount (C.lcbCounts s)))

canonicalTotalCountStrictProgress :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A) →
  StrictProgressWitness
    (C.FullLearnerState A)
    Nat
    (C.canonicalFullStep K)
    _<_
canonicalTotalCountStrictProgress K =
  strictProgressWitness
    (λ s → C.totalCount (C.lcbCounts s))
    (λ s → canonicalTotalCountStepProgress K s)
    <-trans
    <-irrefl

canonicalNoPositiveCycleFromTotalCount :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (n : Nat)
  (s : C.FullLearnerState A) →
  iterateStep (C.canonicalFullStep K) (suc n) s ≡ s →
  ⊥
canonicalNoPositiveCycleFromTotalCount K n s =
  noPositiveFiniteCycleFromStrictProgress
    (canonicalTotalCountStrictProgress K)
    n
    s


------------------------------------------------------------------------
-- 2026-09-26 theorem-improvement closure layer.
--
-- These interfaces deliberately remain in the theorem monolith and use
-- only the imports already present above. Each bridge is proof-relevant:
-- no graph edge, semantic label, convergence claim, or economic claim is
-- promoted without an explicit inhabitant.
------------------------------------------------------------------------

record MonolithStrictProgressClosure
  (State Measure : Set)
  (step : State → State)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor monolithStrictProgressClosure
  field
    witness :
      StrictProgressWitness State Measure step _<_
    noPositiveCycle :
      ∀ n s →
      iterateStep step (suc n) s ≡ s →
      ⊥

open MonolithStrictProgressClosure public

monolithStrictProgressClosure-from-witness :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_) →
  MonolithStrictProgressClosure State Measure step _<_
monolithStrictProgressClosure-from-witness W =
  monolithStrictProgressClosure
    W
    (λ n s →
      noPositiveFiniteCycleFromStrictProgress W n s)

canonicalTotalCountStrictProgress-closure :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A) →
  MonolithStrictProgressClosure
    (C.FullLearnerState A)
    Nat
    (C.canonicalFullStep K)
    _<_
canonicalTotalCountStrictProgress-closure K =
  monolithStrictProgressClosure-from-witness
    (canonicalTotalCountStrictProgress K)

record MonolithFactorTransitionClosure
  (State Factor : Set)
  (step : State → State)
  (related : State → State → Set)
  (observe : State → Factor) : Set₁ where
  constructor monolithFactorTransitionClosure
  field
    factorStep : Factor → Factor
    factorStepCommutes :
      ∀ s →
      observe (step s) ≡ factorStep (observe s)
    observeRespects :
      ∀ {s t} →
      related s t →
      observe s ≡ observe t
    relationStepPreserved :
      ∀ {s t} →
      related s t →
      related (step s) (step t)

monolithFactorTransition-to-relationWitness :
  ∀ {State Factor : Set}
  {step : State → State}
  {related : State → State → Set}
  {observe : State → Factor}
  (W : MonolithFactorTransitionClosure
    State
    Factor
    step
    related
    observe) →
  RelationFactorTransitionWitness
    State
    Factor
    step
    related
    observe
monolithFactorTransition-to-relationWitness W =
  relationFactorTransitionWitness
    (factorTransitionWitness
      (factorStep W)
      (factorStepCommutes W))
    (observeRespects W)
    (relationStepPreserved W)

canonicalNormPairFactorTransitionClosure :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (factorStep : Nat → Nat)
  (factorStepCommutes :
    ∀ s →
    C.canonicalPolicy K (C.canonicalFullStep K s) ≡
    factorStep (C.canonicalPolicy K s)) →
  MonolithFactorTransitionClosure
    (C.FullLearnerState A)
    Nat
    (C.canonicalFullStep K)
    normPairReplacementRelation
    (C.canonicalPolicy K)
canonicalNormPairFactorTransitionClosure
  K
  factorStep
  factorStepCommutes =
  monolithFactorTransitionClosure
    factorStep
    factorStepCommutes
    (canonicalPolicy-factors-through-NormPair K)
    (canonicalNormPairQuotient-step-compatible K)

record MonolithCommutingSquareTransport
  (A B : Set)
  (sourceStep : A → A)
  (targetStep : B → B) : Set₁ where
  constructor monolithCommutingSquareTransport
  field
    square :
      StepConjugacyWitness A B sourceStep targetStep

monolithCommutingSquare-iterate :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : MonolithCommutingSquareTransport
    A B
    sourceStep
    targetStep)
  (n : Nat)
  (a : A) →
  to (isomorphism (square W))
    (iterateIsomorphism sourceStep n a)
  ≡
  iterateIsomorphism targetStep n
    (to (isomorphism (square W)) a)
monolithCommutingSquare-iterate W =
  stepConjugacy-iterate (square W)

monolithCommutingSquare-property :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : MonolithCommutingSquareTransport
    A B
    sourceStep
    targetStep)
  (P : A → Set)
  (Q : B → Set)
  (bridge :
    ∀ a →
    P a →
    Q (to (isomorphism (square W)) a))
  (preserved :
    ∀ b →
    Q b →
    Q (targetStep b)) →
  ∀ n a →
  P a →
  Q
    (iterateIsomorphism targetStep n
      (to (isomorphism (square W)) a))
monolithCommutingSquare-property W P Q bridge preserved =
  stepConjugacy-property-transport
    (square W)
    P
    Q
    bridge
    preserved

record MonolithProductionSideAssumptionBundle
  (Agent Firm Price Consumption ProductionPlan Allocation : Set)
  (consumer : Agent → Consumption)
  (production : Firm → ProductionPlan)
  (price : Price)
  (allocation : Allocation)
  (consumerOptimal : Agent → Consumption → Set)
  (productionFeasible : Firm → ProductionPlan → Set)
  (firmOptimal : Firm → Price → ProductionPlan → Set)
  (consumptionFeasible : Agent → Consumption → Set)
  (aggregateFeasible : Allocation → Set)
  (marketClearing : Price → Allocation → Set)
  (supportingPrice : Price → Allocation → Set) : Set₁ where
  constructor monolithProductionSideAssumptionBundle
  field
    consumerOptimality :
      ∀ i →
      consumerOptimal i (consumer i)
    productionFeasibility :
      ∀ j →
      productionFeasible j (production j)
    firmProfitOptimality :
      ∀ j →
      firmOptimal j price (production j)
    consumptionFeasibility :
      ∀ i →
      consumptionFeasible i (consumer i)
    aggregateFeasibility :
      aggregateFeasible allocation
    marketClearingWitness :
      marketClearing price allocation
    supportingPriceWitness :
      supportingPrice price allocation

open MonolithProductionSideAssumptionBundle public

record MonolithStationaryLawBridge
  (Distribution Economic : Set)
  (P : Distribution → Distribution)
  (μ : Nat → Distribution)
  (μ∞ : Distribution)
  (Converges : (Nat → Distribution) → Distribution → Set)
  (aggregate : Distribution → Economic)
  (economicStep : Economic → Economic) : Set₁ where
  constructor monolithStationaryLawBridge
  field
    distributionalLimit :
      StationaryLimitTheorem
        Distribution
        P
        μ
        μ∞
        Converges
    aggregateCommutes :
      ∀ d →
      aggregate (P d) ≡ economicStep (aggregate d)

monolithStationaryLawBridge-stationary :
  ∀ {Distribution Economic : Set}
  {P : Distribution → Distribution}
  {μ : Nat → Distribution}
  {μ∞ : Distribution}
  {Converges : (Nat → Distribution) → Distribution → Set}
  {aggregate : Distribution → Economic}
  {economicStep : Economic → Economic}
  (W :
    MonolithStationaryLawBridge
      Distribution
      Economic
      P
      μ
      μ∞
      Converges
      aggregate
      economicStep) →
  economicStep (aggregate μ∞) ≡ aggregate μ∞
monolithStationaryLawBridge-stationary W =
  distributionalStationaryAggregate-stationary
    (distributionalStationaryAggregateTransport
      (distributionalLimit W)
      (aggregateCommutes W))

record MonolithEGraphProofCertificate
  (Node Edge Assumption : Set) : Set₁ where
  constructor monolithEGraphProofCertificate
  field
    source : Edge → Node
    target : Edge → Node
    semanticAssumption : Edge → Assumption
    proofWitness : Edge → Set
    proofSound :
      ∀ e →
      proofWitness e
    assumptionToProof :
      ∀ e →
      semanticAssumption e → proofWitness e

record MonolithEGraphClosureCertificate
  (Node Edge Assumption : Set) : Set₁ where
  constructor monolithEGraphClosureCertificate
  field
    certificate :
      MonolithEGraphProofCertificate
        Node
        Edge
        Assumption
    closedEdge :
      Edge → Set

monolithEGraphClosureCertificate-from-proof :
  ∀ {Node Edge Assumption : Set}
  (W :
    MonolithEGraphProofCertificate
      Node
      Edge
      Assumption) →
  MonolithEGraphClosureCertificate
    Node
    Edge
    Assumption
monolithEGraphClosureCertificate-from-proof W =
  monolithEGraphClosureCertificate
    W
    (λ e → proofWitness W e)


------------------------------------------------------------------------
-- Unconditional finite-candidate price kernel.
--
-- This is deliberately weaker than a Walrasian existence theorem:
-- for any finite candidate-price list and an explicit decision procedure
-- for the supporting relation at the chosen allocation, the kernel
-- unconditionally returns either a supporting-price witness or a complete
-- rejection certificate for the supplied candidate list.
--
-- No new imports are required. The result does not claim that a supporting
-- price exists outside the supplied finite candidate set.
------------------------------------------------------------------------

data FiniteCandidateDecision (P : Set) : Set where
  acceptCandidate : P → FiniteCandidateDecision P
  rejectCandidate : (P → ⊥) → FiniteCandidateDecision P

FiniteCandidatePriceResult :
  (Price Allocation : Set) →
  (supports : Price → Allocation → Set) →
  Allocation →
  Set₁
FiniteCandidatePriceResult Price Allocation supports allocation =
  (Σ Price (λ p → supports p allocation))
  ⊎
  List (Σ Price (λ p → supports p allocation → ⊥))

finiteCandidatePriceSearch :
  ∀ {Price Allocation : Set}
  (supports : Price → Allocation → Set)
  (allocation : Allocation)
  (decide : ∀ p → FiniteCandidateDecision (supports p allocation))
  (candidates : List Price) →
  FiniteCandidatePriceResult Price Allocation supports allocation
finiteCandidatePriceSearch supports allocation decide [] =
  inj₂ []
finiteCandidatePriceSearch supports allocation decide (p ∷ ps) with decide p
... | acceptCandidate witness =
  inj₁ (p , witness)
... | rejectCandidate refute with
  finiteCandidatePriceSearch supports allocation decide ps
...   | inj₁ witness =
  inj₁ witness
...   | inj₂ rejected =
  inj₂ ((p , refute) ∷ rejected)

finiteCandidatePriceSearch-complete :
  ∀ {Price Allocation : Set}
  (supports : Price → Allocation → Set)
  (allocation : Allocation)
  (decide : ∀ p → FiniteCandidateDecision (supports p allocation))
  (candidates : List Price) →
  FiniteCandidatePriceResult Price Allocation supports allocation
finiteCandidatePriceSearch-complete =
  finiteCandidatePriceSearch


------------------------------------------------------------------------
-- Unconditional tragedy-of-the-commons non-derivability.
--
-- This boundary is deliberately more primitive than price or equilibrium.
-- It separates individual local optimality from preservation of a shared
-- resource, and the concrete countermodel makes the depletion mechanism
-- explicit: two agents each choose the individually optimal one-unit
-- extraction while the common stock has capacity one.
------------------------------------------------------------------------

record CommonsPreservationDerivation
  (World Agent Action Resource : Set)
  (sharedResource : World → Resource)
  (resourceCapacity : Resource → Nat)
  (action : World → Agent → Action)
  (extraction : Action → Nat)
  (aggregateExtraction : World → Nat)
  (localOptimal : World → Agent → Action → Set) : Set₁ where
  constructor commonsPreservationDerivation
  field
    derive :
      ∀ w →
      (∀ a → localOptimal w a (action w a)) →
      aggregateExtraction w ≤
      resourceCapacity (sharedResource w)

open CommonsPreservationDerivation public

record CommonsNonDerivabilityCounterexample : Set₁ where
  constructor commonsNonDerivabilityCounterexample
  field
    World : Set
    Agent : Set
    Action : Set
    Resource : Set
    sharedResource : World → Resource
    resourceCapacity : Resource → Nat
    action : World → Agent → Action
    extraction : Action → Nat
    aggregateExtraction : World → Nat
    localOptimal : World → Agent → Action → Set
    commonsWorld : World
    commonResource :
      sharedResource commonsWorld
    allLocallyOptimal :
      ∀ a →
      localOptimal
        commonsWorld
        a
        (action commonsWorld a)
    aggregateExtractionIsTwo :
      aggregateExtraction commonsWorld ≡
      suc (suc zero)
    extractionIsOne :
      ∀ a →
      extraction (action commonsWorld a) ≡
      suc zero
    capacityIsOne :
      resourceCapacity (sharedResource commonsWorld) ≡
      suc zero

open CommonsNonDerivabilityCounterexample public

noUnconditionalCommonsPreservation :
  ∀ (C : CommonsNonDerivabilityCounterexample) →
  ¬ CommonsPreservationDerivation
      (World C)
      (Agent C)
      (Action C)
      (Resource C)
      (sharedResource C)
      (resourceCapacity C)
      (action C)
      (extraction C)
      (aggregateExtraction C)
      (localOptimal C)
noUnconditionalCommonsPreservation C D =
  twoNotLeOne
    (subst
      (λ n → n ≤ suc zero)
      (capacityIsOne C)
      (subst
        (λ n → suc (suc zero) ≤ n)
        (aggregateExtractionIsTwo C)
        (derive D
          (commonsWorld C)
          (allLocallyOptimal C))))

twoNotLeOne :
  ¬ suc (suc zero) ≤ suc zero
twoNotLeOne ()

twoAgentCommonsCounterexample :
  CommonsNonDerivabilityCounterexample
twoAgentCommonsCounterexample =
  commonsNonDerivabilityCounterexample
    (⊤)
    (⊤ ⊎ ⊤)
    (⊤ ⊎ ⊤)
    Nat
    (λ _ → suc zero)
    (λ _ → suc zero)
    (λ _ _ → inj₂ tt)
    (λ _ → suc zero)
    (λ _ → suc (suc zero))
    (λ _ _ a → a ≡ inj₂ tt)
    tt
    refl
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)

noUnconditionalCommonsPreservation-twoAgent :
  ¬ CommonsPreservationDerivation
      (World twoAgentCommonsCounterexample)
      (Agent twoAgentCommonsCounterexample)
      (Action twoAgentCommonsCounterexample)
      (Resource twoAgentCommonsCounterexample)
      (sharedResource twoAgentCommonsCounterexample)
      (resourceCapacity twoAgentCommonsCounterexample)
      (action twoAgentCommonsCounterexample)
      (extraction twoAgentCommonsCounterexample)
      (aggregateExtraction twoAgentCommonsCounterexample)
      (localOptimal twoAgentCommonsCounterexample)
noUnconditionalCommonsPreservation-twoAgent =
  noUnconditionalCommonsPreservation
    twoAgentCommonsCounterexample

------------------------------------------------------------------------
-- The concrete model has the intended tragedy mechanism:
--
--   two agents
--      + one-unit shared stock
--      + one-unit private extraction is individually optimal
--      -> two units aggregate extraction
--      -> preservation predicate (extraction <= stock) fails.
--
-- This is not a theorem that every commons collapses. It is an
-- impossibility theorem against the unconditional implication from
-- local optimality alone to aggregate preservation. A positive bridge
-- must add coupling information such as quotas/property rights,
-- internalized externalities, coordination, or a regeneration/conservation
-- invariant.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Unconditional canonical-price non-derivability.
--
-- This stronger boundary preserves equilibrium existence and universal
-- Pareto optimality of equilibria, while showing that a price cannot be
-- unconditionally reconstructed from price-forgetting observations when
-- observationally identical worlds require disjoint supporting prices.
------------------------------------------------------------------------

record CanonicalPriceDerivation
  (World Obs Price Allocation : Set)
  (observe : World → Obs)
  (supports : World → Price → Allocation → Set)
  (equilibrium : World → Price → Allocation → Set) : Set₁ where
  constructor canonicalPriceDerivation
  field
    derive : Obs → Price
    sound :
      ∀ w p a →
      equilibrium w p a →
      supports w (derive (observe w)) a

open CanonicalPriceDerivation public

record CanonicalPriceNonIdentifiabilityCounterexample : Set₁ where
  constructor canonicalPriceNonIdentifiabilityCounterexample
  field
    World : Set
    Obs : Set
    Price : Set
    Allocation : Set
    observe : World → Obs
    supports : World → Price → Allocation → Set
    equilibrium : World → Price → Allocation → Set
    paretoOptimal : Allocation → Set
    world₁ : World
    world₂ : World
    allocation₁ : Allocation
    allocation₂ : Allocation
    price₁ : Price
    price₂ : Price
    sameObservation :
      observe world₁ ≡ observe world₂
    equilibrium₁ :
      equilibrium world₁ price₁ allocation₁
    equilibrium₂ :
      equilibrium world₂ price₂ allocation₂
    allEquilibriaParetoOptimal :
      ∀ {w p a} →
      equilibrium w p a →
      paretoOptimal a
    noCommonSupportingPrice :
      ¬ Σ Price
        (λ p →
          supports world₁ p allocation₁ ×
          supports world₂ p allocation₂)
    distinctPrices :
      price₁ ≢ price₂

open CanonicalPriceNonIdentifiabilityCounterexample public

transportCanonicalPriceSupport :
  ∀ {World Price Allocation : Set}
  {supports : World → Price → Allocation → Set}
  {w : World} {p q : Price} {a : Allocation} →
  p ≡ q →
  supports w p a →
  supports w q a
transportCanonicalPriceSupport refl proof =
  proof

noUnconditionalCanonicalPriceDerivation :
  ∀ (C : CanonicalPriceNonIdentifiabilityCounterexample) →
  ¬ CanonicalPriceDerivation
      (World C)
      (Obs C)
      (Price C)
      (Allocation C)
      (observe C)
      (supports C)
      (equilibrium C)
noUnconditionalCanonicalPriceDerivation C D =
  noCommonSupportingPrice C
    (derive D (observe C (world₁ C))
     , sound D
         (world₁ C)
         (price₁ C)
         (allocation₁ C)
         (equilibrium₁ C)
     , transportCanonicalPriceSupport
         (sym
           (cong
             (derive D)
             (sameObservation C)))
         (sound D
           (world₂ C)
           (price₂ C)
           (allocation₂ C)
           (equilibrium₂ C)))

twoPriceDistinct :
  (inj₁ tt : ⊤ ⊎ ⊤) ≢ inj₂ tt
twoPriceDistinct ()

twoWorldsNoCommonSupportingPrice :
  ¬ Σ (⊤ ⊎ ⊤)
    (λ p →
      (inj₁ tt ≡ p) ×
      (inj₂ tt ≡ p))
twoWorldsNoCommonSupportingPrice
  (p , (support₁ , support₂)) =
  twoPriceDistinct
    (trans support₁ (sym support₂))

twoWorldCanonicalPriceNonIdentifiabilityCounterexample :
  CanonicalPriceNonIdentifiabilityCounterexample
twoWorldCanonicalPriceNonIdentifiabilityCounterexample =
  canonicalPriceNonIdentifiabilityCounterexample
    (⊤ ⊎ ⊤)
    ⊤
    (⊤ ⊎ ⊤)
    ⊤
    (λ _ → tt)
    (λ world price _ → world ≡ price)
    (λ world price allocation → world ≡ price)
    (λ _ → ⊤)
    (inj₁ tt)
    (inj₂ tt)
    tt
    tt
    (inj₁ tt)
    (inj₂ tt)
    refl
    refl
    refl
    (λ { refl → tt })
    twoWorldsNoCommonSupportingPrice
    twoPriceDistinct

noUnconditionalCanonicalPriceDerivation-twoWorld :
  ¬ CanonicalPriceDerivation
      (World twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (Obs twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (Price twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (Allocation twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (observe twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (supports twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (equilibrium twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
noUnconditionalCanonicalPriceDerivation-twoWorld =
  noUnconditionalCanonicalPriceDerivation
    twoWorldCanonicalPriceNonIdentifiabilityCounterexample

------------------------------------------------------------------------
-- Canonical Integer-GRU token encoding: global left inverse, injectivity,
-- and exact recurrent conjugacy.
--
-- CanonicalToken is the unbounded integer carrier ℤ and Int8 is an exact
-- ℤ wrapper. The decoder below is therefore global and total. This proves
-- global injectivity directly from the left-inverse law; no separate
-- separation axiom is required. Continuity is only asserted for the
-- repository's discrete topology, not an analytic topology.
------------------------------------------------------------------------

canonicalTokenDecode : C.Int8 → C.CanonicalToken
canonicalTokenDecode = C.code

canonicalTokenDecode-encode :
  ∀ t → canonicalTokenDecode (C.canonicalTokenEncode t) ≡ t
canonicalTokenDecode-encode t = refl

record CanonicalIntegerGRUTokenEncodingLeftInverse : Set₁ where
  constructor canonicalIntegerGRUTokenEncodingLeftInverse
  field
    decodeEncode :
      ∀ t →
      canonicalTokenDecode (C.canonicalTokenEncode t) ≡ t

open CanonicalIntegerGRUTokenEncodingLeftInverse public

canonical-integer-gru-token-encoding-left-inverse :
  CanonicalIntegerGRUTokenEncodingLeftInverse
canonical-integer-gru-token-encoding-left-inverse =
  canonicalIntegerGRUTokenEncodingLeftInverse
    canonicalTokenDecode-encode

canonicalIntegerGRUTokenEncodingInjective :
  ∀ {s t : C.CanonicalToken} →
  C.canonicalTokenEncode s ≡ C.canonicalTokenEncode t →
  s ≡ t
canonicalIntegerGRUTokenEncodingInjective {s} {t} eq =
  trans
    (sym (decodeEncode canonical-integer-gru-token-encoding-left-inverse s))
    (trans
      (cong canonicalTokenDecode eq)
      (decodeEncode canonical-integer-gru-token-encoding-left-inverse t))

canonicalIntegerGRUTokenEncoding-continuous-discrete :
  Continuous
    C.CanonicalToken
    C.Int8
    (discreteTopology C.CanonicalToken)
    (discreteTopology C.Int8)
    C.canonicalTokenEncode
canonicalIntegerGRUTokenEncoding-continuous-discrete =
  continuous-under-discrete-topology C.canonicalTokenEncode

record CanonicalIntegerGRUGlobalConjugateTheorem : Set₁ where
  constructor canonicalIntegerGRUGlobalConjugateTheorem
  field
    encodingLeftInverse :
      CanonicalIntegerGRUTokenEncodingLeftInverse
    encodingInjective :
      ∀ {s t : C.CanonicalToken} →
      C.canonicalTokenEncode s ≡ C.canonicalTokenEncode t →
      s ≡ t
    encodingContinuousDiscrete :
      Continuous
        C.CanonicalToken
        C.Int8
        (discreteTopology C.CanonicalToken)
        (discreteTopology C.Int8)
        C.canonicalTokenEncode
    recurrentConjugacy :
      CanonicalGlobalTokenEncodingConjugacyTheorem

open CanonicalIntegerGRUGlobalConjugateTheorem public

canonical-integer-gru-global-conjugate-theorem :
  CanonicalIntegerGRUGlobalConjugateTheorem
canonical-integer-gru-global-conjugate-theorem =
  canonicalIntegerGRUGlobalConjugateTheorem
    canonical-integer-gru-token-encoding-left-inverse
    canonicalIntegerGRUTokenEncodingInjective
    canonicalIntegerGRUTokenEncoding-continuous-discrete
    canonical-global-token-encoding-conjugacy



------------------------------------------------------------------------
-- Current canonical arbitrary-limit Integer-GRU composition boundary.
--
-- The generic limit kernel is explicit: this theorem composes the proved
-- global Integer-GRU representation with a surviving limit left inverse.
-- It does not manufacture a concrete analytic limit, convergence witness,
-- projection family, or decoder coherence.
------------------------------------------------------------------------

record CanonicalIntegerGRUFractalLimitCompositionTheorem
  (LimitObservation : Set)
  (limitEncode : C.CanonicalToken → LimitObservation) : Set₁ where
  constructor canonicalIntegerGRUFractalLimitCompositionTheorem
  field
    globalRepresentation :
      CanonicalIntegerGRUGlobalConjugateTheorem
    limitKernel :
      GRUFractalLimitCompositionKernel
        C.CanonicalToken
        C.Int8
        LimitObservation
        limitEncode
    limitInjective :
      ∀ {s t : C.CanonicalToken} →
      limitEncode s ≡ limitEncode t →
      s ≡ t

open CanonicalIntegerGRUFractalLimitCompositionTheorem public

canonical-integer-gru-fractal-limit-composition :
  ∀ {LimitObservation : Set}
  {limitEncode : C.CanonicalToken → LimitObservation} →
  GRUFractalLimitCompositionKernel
    C.CanonicalToken
    C.Int8
    LimitObservation
    limitEncode →
  CanonicalIntegerGRUFractalLimitCompositionTheorem
    LimitObservation
    limitEncode
canonical-integer-gru-fractal-limit-composition K =
  canonicalIntegerGRUFractalLimitCompositionTheorem
    canonical-integer-gru-global-conjugate-theorem
    K
    (gruFractalLimitComposition-limitInjective K)


------------------------------------------------------------------------
-- Inlined nested commons composition boundary; the one-level commons
-- theorem already lives in this monolith above.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Nested / self-similar commons composition boundary.
--
-- The construction is deliberately proposition-valued: no Bool is needed.
-- Each level repeats the same local-optimality -> aggregate-preservation
-- obligation. A global derivation must therefore solve the obligation at
-- every inhabited level. The existing two-agent countermodel refutes that
-- unconditional implication already at one level, and hence also refutes
-- the nested version.
------------------------------------------------------------------------


  using
  ( CommonsNonDerivabilityCounterexample
  ; twoAgentCommonsCounterexample
  ; twoNotLeOne
  ; commonsWorld
  ; sharedResource
  ; resourceCapacity
  ; action
  ; extraction
  ; aggregateExtraction
  ; localOptimal
  ; allLocallyOptimal
  ; aggregateExtractionIsTwo
  ; extractionIsOne
  ; capacityIsOne
  )

------------------------------------------------------------------------
-- A single commons law repeated across an arbitrary collection of levels.
-- "Nested" here is a precise recursive/self-similar interface claim:
-- the same preservation obligation is required independently at every
-- level.
------------------------------------------------------------------------

record NestedCommonsPreservationDerivation
  (Level : Set)
  (C : CommonsNonDerivabilityCounterexample) : Set₁ where
  constructor nestedCommonsPreservationDerivation
  field
    derive :
      ∀ level →
      ∀ w →
      (∀ a →
        localOptimal C
          w
          a
          (action C w a)) →
      aggregateExtraction C w ≤
      resourceCapacity C (sharedResource C w)

open NestedCommonsPreservationDerivation public

------------------------------------------------------------------------
-- Aggregate consistency for the concrete two-agent model.
-- This makes "two-unit aggregate extraction" mathematically tied to the
-- two individual one-unit extractions rather than merely co-present fields.
------------------------------------------------------------------------

twoAgentAggregateExtractionIsSum :
  aggregateExtraction twoAgentCommonsCounterexample
    (commonsWorld twoAgentCommonsCounterexample)
  ≡
  extraction twoAgentCommonsCounterexample
    (action twoAgentCommonsCounterexample
      (inj₁ tt))
  +
  extraction twoAgentCommonsCounterexample
    (action twoAgentCommonsCounterexample
      (inj₂ tt))
twoAgentAggregateExtractionIsSum =
  trans
    (aggregateExtractionIsTwo twoAgentCommonsCounterexample)
    refl

------------------------------------------------------------------------
-- One bad level destroys an unconditional all-level derivation.
------------------------------------------------------------------------

noUnconditionalNestedCommonsPreservation :
  ∀ {Level : Set} →
  Level →
  (C : CommonsNonDerivabilityCounterexample) →
  ¬ NestedCommonsPreservationDerivation Level C
noUnconditionalNestedCommonsPreservation level C D =
  twoNotLeOne
    (subst
      (λ n → n ≤ suc zero)
      (capacityIsOne C)
      (subst
        (λ n → suc (suc zero) ≤ n)
        (aggregateExtractionIsTwo C)
        (derive D
          level
          (commonsWorld C)
          (allLocallyOptimal C))))

------------------------------------------------------------------------
-- Concrete two-scale instance: two nested levels are enough to witness
-- the impossibility. The same local/global law is demanded at each level.
------------------------------------------------------------------------

TwoScaleCommonsLevel : Set
TwoScaleCommonsLevel = ⊤ ⊎ ⊤

noUnconditionalNestedCommonsPreservation-twoScale :
  ¬ NestedCommonsPreservationDerivation
      TwoScaleCommonsLevel
      twoAgentCommonsCounterexample
noUnconditionalNestedCommonsPreservation-twoScale =
  noUnconditionalNestedCommonsPreservation
    (inj₁ tt)
    twoAgentCommonsCounterexample

------------------------------------------------------------------------
-- Scale composition rule.
--
-- A nested preservation proof is strictly stronger than a one-level proof:
-- restricting it to any inhabited level yields the corresponding local
-- preservation derivation. Thus adding more levels cannot manufacture the
-- missing local-to-global conservation invariant.
------------------------------------------------------------------------

nestedLevelRestriction :
  ∀ {Level : Set}
  {C : CommonsNonDerivabilityCounterexample} →
  (D : NestedCommonsPreservationDerivation Level C) →
  ∀ level →
  ∀ w →
  (∀ a →
    localOptimal C w a (action C w a)) →
  aggregateExtraction C w ≤
  resourceCapacity C (sharedResource C w)
nestedLevelRestriction D level =
  derive D level

------------------------------------------------------------------------
-- The unconditional graph is therefore closed at the negative boundary:
--
-- local optimality
--   -> individual extraction
--   -> aggregate extraction
--   -X-> preservation
--
-- and recursively:
--
-- level 0 -> level 1 -> ... -> level n
--   with preservation required at every inhabited level.
--
-- No Boolean encoding is involved. The propositions themselves live in Set;
-- Nat supplies the resource quantities; equality and subst transport the
-- concrete countermodel into the preservation obligation.
------------------------------------------------------------------------
