{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.ConnectedOperatorCompositionComplexity where

open import Data.Nat using (Nat; zero; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; +-mono-≤; *-suc)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)

------------------------------------------------------------------------
-- Structural operator layer only.
------------------------------------------------------------------------

record Operator (S : Set) : Set where
  constructor operator
  field
    run : S → S
    representationSize : Nat
    applicationCost : Nat

open Operator public

identityOperator : ∀ {S : Set} → Operator S
identityOperator = operator (λ s → s) zero zero

composeOperator : ∀ {S : Set} → Operator S → Operator S → Operator S
composeOperator f g =
  operator
    (λ s → run f (run g s))
    (representationSize f + representationSize g)
    (applicationCost f + applicationCost g)

composeOperator-law :
  ∀ {S : Set} (f g : Operator S) (s : S) →
  run (composeOperator f g) s ≡ run f (run g s)
composeOperator-law f g s = refl

composeOperator-size :
  ∀ {S : Set} (f g : Operator S) →
  representationSize (composeOperator f g) ≡
  representationSize f + representationSize g
composeOperator-size f g = refl

composeOperator-cost :
  ∀ {S : Set} (f g : Operator S) →
  applicationCost (composeOperator f g) ≡
  applicationCost f + applicationCost g
composeOperator-cost f g = refl

composeOperator-associative :
  ∀ {S : Set} (f g h : Operator S) (s : S) →
  run (composeOperator (composeOperator f g) h) s ≡
  run (composeOperator f (composeOperator g h)) s
composeOperator-associative f g h s = refl

composeOperator-size-associative :
  ∀ {S : Set} (f g h : Operator S) →
  representationSize (composeOperator (composeOperator f g) h) ≡
  representationSize (composeOperator f (composeOperator g h))
composeOperator-size-associative f g h =
  +-assoc (representationSize f) (representationSize g) (representationSize h)

composeOperator-cost-associative :
  ∀ {S : Set} (f g h : Operator S) →
  applicationCost (composeOperator (composeOperator f g) h) ≡
  applicationCost (composeOperator f (composeOperator g h))
composeOperator-cost-associative f g h =
  +-assoc (applicationCost f) (applicationCost g) (applicationCost h)

------------------------------------------------------------------------
-- Component budgets.  NormPair and F4 may each supply an instance of
-- this certificate without entering the structural module.
------------------------------------------------------------------------

record BoundedOperator (S : Set) : Set where
  constructor boundedOperator
  field
    operator : Operator S
    budget : Nat
    size≤budget : representationSize operator ≤ budget

open BoundedOperator public

boundedComposition :
  ∀ {S} (f g : BoundedOperator S) →
  representationSize (composeOperator (operator f) (operator g)) ≤
  budget f + budget g
boundedComposition f g =
  +-mono-≤ (size≤budget f) (size≤budget g)

------------------------------------------------------------------------
-- A fixed input selects an endomorphism.  This is the precise
-- state-independent representation boundary for associative scans.
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
  Operator S
operatorAt K x =
  operator
    (step K x)
    (representationSizeAt K x)
    (applicationCostAt K x)

------------------------------------------------------------------------
-- Sequential trace representation and exact cost.
------------------------------------------------------------------------

traceOperator :
  ∀ {A S : Set} →
  (A → Operator S) →
  List A →
  Operator S
traceOperator step [] = identityOperator
traceOperator step (x ∷ xs) =
  composeOperator (traceOperator step xs) (step x)

traceRun :
  ∀ {A S : Set} →
  (A → Operator S) →
  List A →
  S →
  S
traceRun step [] s = s
traceRun step (x ∷ xs) s =
  traceRun step xs (run (step x) s)

trace-encoding :
  ∀ {A S : Set} (step : A → Operator S) (xs : List A) (s : S) →
  run (traceOperator step xs) s ≡ traceRun step xs s
trace-encoding step [] s = refl
trace-encoding step (x ∷ xs) s =
  trans
    (composeOperator-law (traceOperator step xs) (step x) s)
    (trace-encoding step xs (run (step x) s))

traceSize :
  ∀ {A S : Set} →
  (A → Operator S) →
  List A →
  Nat
traceSize step [] = zero
traceSize step (x ∷ xs) =
  traceSize step xs + representationSize (step x)

traceCost :
  ∀ {A S : Set} →
  (A → Operator S) →
  List A →
  Nat
traceCost step [] = zero
traceCost step (x ∷ xs) =
  traceCost step xs + applicationCost (step x)

traceOperator-size :
  ∀ {A S : Set} (step : A → Operator S) (xs : List A) →
  representationSize (traceOperator step xs) ≡ traceSize step xs
traceOperator-size step [] = refl
traceOperator-size step (x ∷ xs) =
  cong
    (λ n → n + representationSize (step x))
    (traceOperator-size step xs)

traceOperator-cost :
  ∀ {A S : Set} (step : A → Operator S) (xs : List A) →
  applicationCost (traceOperator step xs) ≡ traceCost step xs
traceOperator-cost step [] = refl
traceOperator-cost step (x ∷ xs) =
  cong
    (λ n → n + applicationCost (step x))
    (traceOperator-cost step xs)

listLength : ∀ {A} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

traceCost-bound :
  ∀ {A S : Set}
  (step : A → Operator S)
  (C : Nat)
  (xs : List A) →
  (∀ x → applicationCost (step x) ≤ C) →
  traceCost step xs ≤
  C * listLength xs
traceCost-bound step C [] bound = z≤n
traceCost-bound step C (x ∷ xs) bound =
  subst
    (λ n → traceCost step xs + applicationCost (step x) ≤ n)
    (trans
      (sym (+-comm C (C * listLength xs)))
      (sym (*-suc C (listLength xs))))
    (+-mono-≤
      (traceCost-bound step C xs bound)
      (bound x))

------------------------------------------------------------------------
-- Explicit encoding + simulation certificate.
------------------------------------------------------------------------

iterate :
  ∀ {S X : Set} →
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
  ∀ {S T X : Set}
  {sourceStep : X → S → S}
  {target : ConnectedOperatorFamily T X}
  {encode : S → T} →
  SimulationCertificate sourceStep target encode →
  ∀ xs s →
  encode (iterate sourceStep xs s) ≡
  run (traceOperator (operatorAt target) xs) (encode s)
simulate C [] s = refl
simulate C (x ∷ xs) s =
  trans
    (simulate C xs (sourceStep x s))
    (trans
      (cong
        (run (traceOperator (operatorAt target) xs))
        (stepSimulation C x s))
      (sym
        (composeOperator-law
          (traceOperator (operatorAt target) xs)
          (operatorAt target x)
          (encode s))))
