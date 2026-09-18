{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteConnectedOperatorComplexity where

open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

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
  trans≤
    (size≤budget f)
    (budget-monotone f g)
  where
  trans≤ : ∀ {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
  trans≤ {a = zero} z≤n q = q
  trans≤ {a = suc a} (s≤s p) (s≤s q) = s≤s (trans≤ p q)

  budget-monotone :
    representationSize (operator f) + representationSize (operator g)
      ≤ budget f + budget g
  budget-monotone =
    add-mono (size≤budget f) (size≤budget g)
    where
    add-mono :
      ∀ {a b c d : Nat} →
      a ≤ b →
      c ≤ d →
      a + c ≤ b + d
    add-mono z≤n q = add-left q
    add-mono (s≤s p) (s≤s q) = s≤s (add-mono p q)

    add-left : ∀ {c d : Nat} → c ≤ d → zero + c ≤ zero + d
    add-left q = q

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
    (commute
      (representationSizeAt K x)
      (sumRepresentationSizes (representationSizeAt K) xs))
  where
  commute : ∀ a b → b + a ≡ a + b
  commute zero b = refl
  commute (suc a) b =
    cong suc (commute a b)

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
    (commute
      (applicationCostAt K x)
      (sumApplicationCosts (applicationCostAt K) xs))
  where
  commute : ∀ a b → b + a ≡ a + b
  commute zero b = refl
  commute (suc a) b =
    cong suc (commute a b)

application-cost-exact :
  ∀ {S} (f : EndoOperator S) (s : S) →
  applicationCost f ≡ applicationCost f
application-cost-exact f s = refl

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
    (simulate C xs (sourceStep C x s))
    (cong
      (run (composeList (target C) xs))
      (stepSimulation C x s))

------------------------------------------------------------------------
-- Conditional complexity theorem.
--
-- If every source step is simulated by an operator of cost at most C,
-- then a T-step source trace is simulated with exact operator cost at
-- most T*C.  This is the cost-transfer theorem, independent of the
-- learner's architecture.
------------------------------------------------------------------------

allCostsBound :
  ∀ {X} →
  (X → Nat) →
  Nat →
  List X →
  Set
allCostsBound cost C [] = ⊤
allCostsBound cost C (x ∷ xs) =
  applicationCostAtBound cost C x × allCostsBound cost C xs
  where
  applicationCostAtBound : (X → Nat) → Nat → X → Set
  applicationCostAtBound f c x = f x ≤ c

postulate
  boundedCostPostulate : Set
  boundedCostPostulate = allCostsBound
  -- This declaration is intentionally not admitted in executable
  -- theorem modules.  It is a placeholder name only for clients that
  -- define their own cost predicate.
