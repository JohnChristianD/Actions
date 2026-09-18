{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteConnectedOperatorComplexity where

open import Agda.Builtin.Nat using (Nat; zero; _+_; _≤_; z≤n; s≤s)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)
open import Data.Nat.Properties using (+-comm; +-mono-≤)

------------------------------------------------------------------------
-- Structural layer only.
--
-- An EndoOperator carries:
--   1. its semantic endofunction,
--   2. a representation-size certificate,
--   3. an application-cost certificate.
--
-- The size and cost fields are a declared exact cost model.  They are
-- not silently identified with hardware instruction counts.
------------------------------------------------------------------------

record EndoOperator (S : Set) : Set where
  constructor endoOperator
  field
    run : S → S
    representationSize : Nat
    applicationCost : Nat
open EndoOperator public

identityOperator : ∀ {S} → EndoOperator S
identityOperator = endoOperator (λ s → s) zero zero

_∘ₒ_ : ∀ {S} → EndoOperator S → EndoOperator S → EndoOperator S
f ∘ₒ g =
  endoOperator
    (λ s → run f (run g s))
    (representationSize f + representationSize g)
    (applicationCost f + applicationCost g)

composition-size :
  ∀ {S} (f g : EndoOperator S) →
  representationSize (f ∘ₒ g) ≡
  representationSize f + representationSize g
composition-size f g = refl

composition-cost :
  ∀ {S} (f g : EndoOperator S) →
  applicationCost (f ∘ₒ g) ≡
  applicationCost f + applicationCost g
composition-cost f g = refl

composition-assoc-pointwise :
  ∀ {S} (f g h : EndoOperator S) (s : S) →
  run ((f ∘ₒ g) ∘ₒ h) s ≡ run (f ∘ₒ (g ∘ₒ h)) s
composition-assoc-pointwise f g h s = refl

------------------------------------------------------------------------
-- A connected recurrent kernel is state-independent at the
-- representation level: fixing an input x selects one endomorphism.
------------------------------------------------------------------------

record ConnectedOperatorFamily (S X : Set) : Set where
  constructor connectedOperatorFamily
  field
    step : X → S → S
    representationSizeAt : X → Nat
    applicationCostAt : X → Nat
open ConnectedOperatorFamily public

operatorAt :
  ∀ {S X} →
  ConnectedOperatorFamily S X →
  X →
  EndoOperator S
operatorAt K x =
  endoOperator
    (step K x)
    (representationSizeAt K x)
    (applicationCostAt K x)

------------------------------------------------------------------------
-- Explicit size/cost composition bounds for components such as
-- recurrent, F4, and NormPair-bounded pieces.
------------------------------------------------------------------------

record BoundedOperator (S : Set) : Set where
  constructor boundedOperator
  field
    operator : EndoOperator S
    budget : Nat
    size≤budget : representationSize operator ≤ budget
open BoundedOperator public

bounded-composition :
  ∀ {S} (f g : BoundedOperator S) →
  representationSize (operator f ∘ₒ operator g)
    ≤ budget f + budget g
bounded-composition f g =
  +-mono-≤ (size≤budget f) (size≤budget g)

------------------------------------------------------------------------
-- Exact sequential composition cost.
------------------------------------------------------------------------

composeList :
  ∀ {S X} →
  ConnectedOperatorFamily S X →
  List X →
  EndoOperator S
composeList K [] = identityOperator
composeList K (x ∷ xs) =
  composeList K xs ∘ₒ operatorAt K x

sumRepresentationSizes :
  ∀ {X} →
  (X → Nat) →
  List X →
  Nat
sumRepresentationSizes size [] = zero
sumRepresentationSizes size (x ∷ xs) =
  size x + sumRepresentationSizes size xs

sumApplicationCosts :
  ∀ {X} →
  (X → Nat) →
  List X →
  Nat
sumApplicationCosts cost [] = zero
sumApplicationCosts cost (x ∷ xs) =
  cost x + sumApplicationCosts cost xs

composeList-size :
  ∀ {S X} (K : ConnectedOperatorFamily S X) (xs : List X) →
  representationSize (composeList K xs) ≡
  sumRepresentationSizes (representationSizeAt K) xs
composeList-size K [] = refl
composeList-size K (x ∷ xs) =
  trans
    (cong
      (λ n → n + representationSizeAt K x)
      (composeList-size K xs))
    (+-comm
      (sumRepresentationSizes (representationSizeAt K) xs)
      (representationSizeAt K x))

composeList-cost :
  ∀ {S X} (K : ConnectedOperatorFamily S X) (xs : List X) →
  applicationCost (composeList K xs) ≡
  sumApplicationCosts (applicationCostAt K) xs
composeList-cost K [] = refl
composeList-cost K (x ∷ xs) =
  trans
    (cong
      (λ n → n + applicationCostAt K x)
      (composeList-cost K xs))
    (+-comm
      (sumApplicationCosts (applicationCostAt K) xs)
      (applicationCostAt K x))

application-cost-exact :
  ∀ {S} (f : EndoOperator S) (s : S) →
  applicationCost f ≡ applicationCost f
application-cost-exact f s = refl

sumRepresentationSizes-bound :
  ∀ {S X}
  (K : ConnectedOperatorFamily S X)
  (B : Nat)
  (xs : List X) →
  (∀ x → representationSizeAt K x ≤ B) →
  sumRepresentationSizes (representationSizeAt K) xs ≤
  B * listLength xs
sumRepresentationSizes-bound K B [] bound = z≤n
sumRepresentationSizes-bound K B (x ∷ xs) bound =
  subst
    (λ n →
      representationSizeAt K x +
      sumRepresentationSizes (representationSizeAt K) xs
      ≤ n)
    (sym (*-suc B (listLength xs)))
    (+-mono-≤
      (bound x)
      (sumRepresentationSizes-bound K B xs bound))

sumApplicationCosts-bound :
  ∀ {S X}
  (K : ConnectedOperatorFamily S X)
  (C : Nat)
  (xs : List X) →
  (∀ x → applicationCostAt K x ≤ C) →
  sumApplicationCosts (applicationCostAt K) xs ≤
  C * listLength xs
sumApplicationCosts-bound K C [] bound = z≤n
sumApplicationCosts-bound K C (x ∷ xs) bound =
  subst
    (λ n →
      applicationCostAt K x +
      sumApplicationCosts (applicationCostAt K) xs
      ≤ n)
    (sym (*-suc C (listLength xs)))
    (+-mono-≤
      (bound x)
      (sumApplicationCosts-bound K C xs bound))

------------------------------------------------------------------------
-- Explicit encoding + step simulation.
--
-- This is the exact proof boundary needed for a universal simulator:
-- supply an encoding and a per-input commuting square.  The entire
-- finite trace then follows by induction.
------------------------------------------------------------------------

iterate :
  ∀ {S X} →
  (X → S → S) →
  List X →
  S →
  S
iterate step [] s = s
iterate step (x ∷ xs) s =
  iterate step xs (step x s)

record SimulationCertificate
  {S T X : Set}
  (sourceStep : X → S → S)
  (target : ConnectedOperatorFamily T X)
  (encode : S → T) : Set where
  constructor simulationCertificate
  field
    stepSimulation :
      ∀ x s →
      encode (sourceStep x s) ≡ step target x (encode s)
open SimulationCertificate public

simulate :
  ∀ {S T X}
  {sourceStep : X → S → S}
  {target : ConnectedOperatorFamily T X}
  {encode : S → T} →
  SimulationCertificate sourceStep target encode →
  ∀ xs s →
  encode (iterate sourceStep xs s) ≡
  run (composeList target xs) (encode s)
simulate C [] s = refl
simulate C (x ∷ xs) s =
  trans
    (simulate C xs (sourceStep x s))
    (cong
      (run (composeList target xs))
      (stepSimulation C x s))

