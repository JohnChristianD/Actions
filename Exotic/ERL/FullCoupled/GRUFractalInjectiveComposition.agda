{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Generic self-similar/fractal injective-composition kernel.
--
-- "Fractal" is used here only with an explicit level relation and an
-- inter-level transport law. Mere indexing by Level is not treated as
-- fractality.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.GRUFractalInjectiveComposition where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans; sym)

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
