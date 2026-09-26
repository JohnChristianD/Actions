{-# OPTIONS --safe #-}

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

module Exotic.ERL.FullCoupled.GRUFractalEGraphAStarLimitComposition where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)
open import Exotic.ERL.FullCoupled.GRUFractalLimitClosure
open import Exotic.ERL.FullCoupled.EGraphSemanticTransport

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
