{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GRUFractalLimitConvergenceAdapter where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (Nat; zero)

open import Exotic.ERL.FullCoupled.GRUFractalLimitClosure public
open import Exotic.ERL.FullCoupled.GRUFractalLimitDecoderSurvival public
open import Exotic.ERL.FullCoupled.GRUFractalEGraphAStarLimitComposition public

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
