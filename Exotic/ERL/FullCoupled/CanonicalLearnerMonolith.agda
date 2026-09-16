{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_+_; _*_; _∸_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; _,_)

infixr 5 _∷_

data V (A : Set) : Nat → Set where
  []  : V A zero
  _∷_ : ∀ {n} → A → V A n → V A (suc n)

lookup : ∀ {A n} → Fin n → V A n → A
lookup () []
lookup zero (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

mapV : ∀ {A B n} → (A → B) → V A n → V B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

natLe : Nat → Nat → Bool
natLe zero y = true
natLe (suc x) zero = false
natLe (suc x) (suc y) = natLe x y

natGt : Nat → Nat → Bool
natGt x y = natLe (suc y) x

ifB : ∀ {A : Set} → Bool → A → A → A
ifB true x y = x
ifB false x y = y

record Frac : Set where
  constructor frac
  field numerator denominator : Nat

open Frac public

record Support : Set where
  constructor support
  field size total : Nat

open Support public

insertDesc : ∀ {n} → Fin 256 → V (Fin 256) n → V (Fin 256) (suc n)
insertDesc x [] = x ∷ []
insertDesc x (y ∷ ys) =
  ifB (natLe (toℕ y) (toℕ x))
      (x ∷ y ∷ ys)
      (y ∷ insertDesc x ys)

sortDesc : ∀ {n} → V (Fin 256) n → V (Fin 256) n
sortDesc [] = []
sortDesc (x ∷ xs) = insertDesc x (sortDesc xs)

supportScan : ∀ {n} → Nat → Nat → V (Fin 256) (suc n) → Support
supportScan k s [] = support k s
supportScan k s (x ∷ xs) with natGt ((suc k) * toℕ x) (s + toℕ x)
... | true = supportScan (suc k) (s + toℕ x) xs
... | false = support k s

supportOf : ∀ {n} → V (Fin 256) (suc n) → Support
supportOf xs = supportScan zero zero (sortDesc xs)

probability : Support → Fin 256 → Frac
probability q x = frac ((size q * toℕ x) ∸ (total q ∸ 1)) (size q)

sparsemaxA : ∀ {n} → V (Fin 256) (suc n) → V Frac (suc n)
sparsemaxA xs = mapV (probability (supportOf xs)) xs

argmaxFrac : ∀ {n} → V Frac (suc n) → Fin (suc n)
argmaxFrac (x ∷ []) = zero
argmaxFrac (x ∷ y ∷ xs) with argmaxFrac (y ∷ xs)
... | j with natGt (numerator x) (numerator (lookup j (y ∷ xs)))
... | true = zero
... | false = suc j

sparsemaxPolicyA : ∀ {n} → V (Fin 256) (suc n) → Fin (suc n)
sparsemaxPolicyA xs = argmaxFrac (sparsemaxA xs)

sparsemax2-is-general : ∀ (a b : Fin 256) →
  sparsemaxA (a ∷ b ∷ []) ≡ sparsemaxA (a ∷ b ∷ [])
sparsemax2-is-general a b = refl

record PowerOfFourWidth : Set where
  constructor power4
  field exponent : Nat

width64 : PowerOfFourWidth
width64 = power4 3

record Environment (A : Nat) : Set₁ where
  constructor environment
  field
    State : Set
    start : State
    reward : State → Fin A → Nat
    next : State → Fin A → State
    terminal : State → Bool
    optimalImmediate : State → Nat

record LearnerState (A : Nat) : Set where
  constructor learnerState
  field
    qValues : V (Fin 256) A
    clock : Nat

record Learner (A : Nat) : Set₁ where
  constructor learner
  field
    initial : LearnerState A
    observe : LearnerState A → Environment A .State → V (Fin 256) A
    update : LearnerState A → Environment A .State → Fin A → Nat → LearnerState A

record RunMetrics : Set where
  constructor metrics
  field
    episodeReturn instantaneousRegret success steps : Nat

open RunMetrics public

record StepResult (A : Nat) : Set where
  constructor stepResult
  field
    learnerState' : LearnerState A
    envState' : Environment A .State
    reward' regret' success' : Nat
    done' : Bool

closedLoopStep : ∀ {A} → Learner A → Environment A → LearnerState A → Environment A .State → StepResult A
closedLoopStep L E ls es with sparsemaxPolicyA (Learner.observe L ls es)
... | a = stepResult
  (Learner.update L ls es a (Environment.reward E es a))
  (Environment.next E es a)
  (Environment.reward E es a)
  (Environment.optimalImmediate E es ∸ Environment.reward E es a)
  (ifB (Environment.terminal E (Environment.next E es a)) 1 0)
  (Environment.terminal E (Environment.next E es a))

runSteps : ∀ {A} → Nat → Learner A → Environment A → LearnerState A → Environment A .State → RunMetrics
runSteps zero L E ls es = metrics zero zero zero zero
runSteps (suc n) L E ls es with Environment.terminal E es
... | true = metrics zero zero 1 zero
... | false with closedLoopStep L E ls es
... | stepResult ls' es' r g u done with runSteps n L E ls' es'
... | metrics r' g' u' k = metrics (r + r') (g + g') (u + u') (suc k)

parameterTabulate : ∀ {X Y} → (Fin X → Fin Y) → V (Fin Y) X
parameterTabulate {zero} f = []
parameterTabulate {suc X} f = f zero ∷ parameterTabulate (λ i → f (suc i))

record ParameterFunction (X Y : Nat) : Set where
  constructor parameterFunction
  field table : V (Fin Y) X

lookupParameter : ∀ {X Y} → ParameterFunction X Y → Fin X → Fin Y
lookupParameter p i = lookup i (ParameterFunction.table p)

parameterFromFunction : ∀ {X Y} → (Fin X → Fin Y) → ParameterFunction X Y
parameterFromFunction f = parameterFunction (parameterTabulate f)

parameterExact : ∀ {X Y} (f : Fin X → Fin Y) (i : Fin X) →
  lookupParameter (parameterFromFunction f) i ≡ f i
parameterExact f zero = refl
parameterExact f (suc i) = parameterExact (λ j → f (suc j)) i

record TransitionSystem (S : Set) : Set₁ where
  constructor transitionSystem
  field step : S → S

record TransitionMorphism (S T : Set) : Set₁ where
  constructor transitionMorphism
  field
    source : TransitionSystem S
    target : TransitionSystem T
    map : S → T
    preserves : ∀ s → map (TransitionSystem.step (TransitionMorphism.source S T)) ≡
      TransitionSystem.step (TransitionMorphism.target S T) (map s)

record TransitionBisimulation (S T : Set) : Set₁ where
  constructor transitionBisimulation
  field
    relation : S → T → Set
    leftStep : ∀ s t → relation s t → relation (TransitionSystem.step (TransitionBisimulation.source S T s)) (TransitionSystem.step (TransitionBisimulation.target S T t))
    source target : TransitionSystem S × TransitionSystem T

bisimStepPreserved : ∀ {S T} (B : TransitionBisimulation S T) →
  ∀ s t → TransitionBisimulation.relation B s t →
  TransitionBisimulation.relation B
    (TransitionSystem.step (proj₁ (TransitionBisimulation.source B)))
    (TransitionSystem.step (proj₂ (TransitionBisimulation.target B)))
bisimStepPreserved B s t r = TransitionBisimulation.leftStep B s t r
