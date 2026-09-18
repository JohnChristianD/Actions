{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.ConnectedOperatorCompositionComplexity where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

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

traceOperator :
  ∀ {A S : Set} → (A → Operator S) → List A → Operator S
traceOperator step [] = identityOperator
traceOperator step (x ∷ xs) =
  composeOperator (traceOperator step xs) (step x)

traceRun :
  ∀ {A S : Set} (step : A → Operator S) →
  List A → S → S
traceRun step [] s = s
traceRun step (x ∷ xs) s =
  traceRun step xs (run (step x) s)

trace-encoding :
  ∀ {A S : Set} (step : A → Operator S) (xs : List A) (s : S) →
  run (traceOperator step xs) s ≡ traceRun step xs s
trace-encoding step [] s = refl
trace-encoding step (x ∷ xs) s =
  trace-encoding step xs (run (step x) s)

traceSize :
  ∀ {A S : Set} (step : A → Operator S) → List A → Nat
traceSize step [] = zero
traceSize step (x ∷ xs) =
  traceSize step xs + representationSize (step x)

traceCost :
  ∀ {A S : Set} (step : A → Operator S) → List A → Nat
traceCost step [] = zero
traceCost step (x ∷ xs) =
  traceCost step xs + applicationCost (step x)

traceOperator-size :
  ∀ {A S : Set} (step : A → Operator S) (xs : List A) →
  representationSize (traceOperator step xs) ≡ traceSize step xs
traceOperator-size step [] = refl
traceOperator-size step (x ∷ xs) =
  traceOperator-size step xs

traceOperator-cost :
  ∀ {A S : Set} (step : A → Operator S) (xs : List A) →
  applicationCost (traceOperator step xs) ≡ traceCost step xs
traceOperator-cost step [] = refl
traceOperator-cost step (x ∷ xs) =
  traceOperator-cost step xs

traceLearner :
  ∀ {A : Nat} →
  L.LearnerKernel A →
  List L.Int8 →
  L.LearnerState A →
  L.LearnerState A
traceLearner K [] s = s
traceLearner K (r ∷ rs) s =
  traceLearner K rs (L.learnerStep K s r)

learnerStepOperator :
  ∀ {A : Nat} →
  L.LearnerKernel A →
  L.Int8 →
  Nat →
  Operator (L.LearnerState A)
learnerStepOperator K r c =
  operator (λ s → L.learnerStep K s r) 1 c

learnerTraceOperator :
  ∀ {A : Nat} →
  L.LearnerKernel A →
  Nat →
  List L.Int8 →
  Operator (L.LearnerState A)
learnerTraceOperator K c =
  traceOperator (λ r → learnerStepOperator K r c)

learnerTrace-simulates :
  ∀ {A : Nat} (K : L.LearnerKernel A) c (rs : List L.Int8) (s : L.LearnerState A) →
  run (learnerTraceOperator K c rs) s ≡ traceLearner K rs s
learnerTrace-simulates K c [] s = refl
learnerTrace-simulates K c (r ∷ rs) s =
  learnerTrace-simulates K c rs (L.learnerStep K s r)

learnerTrace-size-exact :
  ∀ {A : Nat} (K : L.LearnerKernel A) c (rs : List L.Int8) →
  representationSize (learnerTraceOperator K c rs) ≡
  traceSize (λ r → learnerStepOperator K r c) rs
learnerTrace-size-exact K c rs =
  traceOperator-size (λ r → learnerStepOperator K r c) rs

learnerTrace-cost-exact :
  ∀ {A : Nat} (K : L.LearnerKernel A) c (rs : List L.Int8) →
  applicationCost (learnerTraceOperator K c rs) ≡
  traceCost (λ r → learnerStepOperator K r c) rs
learnerTrace-cost-exact K c rs =
  traceOperator-cost (λ r → learnerStepOperator K r c) rs

gruRingOperationCost : Nat
gruRingOperationCost = 3

gruGateOperationCost : Nat
gruGateOperationCost = 1

gruPrimitiveCost : Nat
gruPrimitiveCost = gruRingOperationCost + gruGateOperationCost

gruStepOperator : L.Int8 → Operator L.GRUState
gruStepOperator x =
  operator
    (λ s → L.gruStep s x)
    1
    gruPrimitiveCost

gruTraceOperator :
  List L.Int8 →
  Operator L.GRUState
gruTraceOperator = traceOperator gruStepOperator

gruTrace-cost-exact :
  ∀ xs →
  applicationCost (gruTraceOperator xs) ≡
  traceCost gruStepOperator xs
gruTrace-cost-exact xs =
  traceOperator-cost gruStepOperator xs
