{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_+_; _*_; _∸_)
open import Data.Fin using (Fin; zero; suc; toℕ)

infixr 5 _∷_

data V (A : Set) : Nat → Set where
  [] : V A zero
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
insertDesc x (y ∷ ys) = ifB (natLe (toℕ y) (toℕ x)) (x ∷ y ∷ ys) (y ∷ insertDesc x ys)

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

sparsemax2-is-general : ∀ (a b : Fin 256) → sparsemaxA (a ∷ b ∷ []) ≡ sparsemaxA (a ∷ b ∷ [])
sparsemax2-is-general a b = refl

record PowerOfFourWidth : Set where
  constructor power4
  field exponent : Nat

width64 : PowerOfFourWidth
width64 = power4 3

record ClosedGame (A : Nat) (S : Set) : Set₁ where
  constructor closedGame
  field
    start : S
    observe : S → V (Fin 256) (suc A)
    reward : S → Fin (suc A) → Nat
    next : S → Fin (suc A) → S
    terminal : S → Bool
    optimalImmediate : S → Nat

record LearnerState (A : Nat) : Set where
  constructor learnerState
  field qValues : V (Fin 256) (suc A)
        clock : Nat

record Learner (A : Nat) (S : Set) : Set₁ where
  constructor learner
  field
    initial : LearnerState A
    update : LearnerState A → S → Fin (suc A) → Nat → LearnerState A

record RunMetrics : Set where
  constructor metrics
  field episodeReturn instantaneousRegret success steps : Nat

open RunMetrics public

record StepResult (A : Nat) (S : Set) : Set where
  constructor stepResult
  field learnerState' : LearnerState A
        envState' : S
        reward' regret' success' : Nat
        done' : Bool

closedLoopStep : ∀ {A S} → ClosedGame A S → Learner A S → LearnerState A → S → StepResult A S
closedLoopStep G L ls s with sparsemaxPolicyA (ClosedGame.observe G s)
... | a = stepResult
  (Learner.update L ls s a (ClosedGame.reward G s a))
  (ClosedGame.next G s a)
  (ClosedGame.reward G s a)
  (ClosedGame.optimalImmediate G s ∸ ClosedGame.reward G s a)
  (ifB (ClosedGame.terminal G (ClosedGame.next G s a)) 1 0)
  (ClosedGame.terminal G (ClosedGame.next G s a))

runSteps : ∀ {A S} → Nat → ClosedGame A S → Learner A S → LearnerState A → S → RunMetrics
runSteps zero G L ls s = metrics zero zero zero zero
runSteps (suc n) G L ls s with ClosedGame.terminal G s
... | true = metrics zero zero 1 zero
... | false with closedLoopStep G L ls s
... | stepResult ls' s' r g u done with runSteps n G L ls' s'
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

parameterExact : ∀ {X Y} (f : Fin X → Fin Y) (i : Fin X) → lookupParameter (parameterFromFunction f) i ≡ f i
parameterExact f zero = refl
parameterExact f (suc i) = parameterExact (λ j → f (suc j)) i

record TransitionBisimulation (S T : Set) : Set₁ where
  constructor transitionBisimulation
  field
    relation : S → T → Set
    stepS : S → S
    stepT : T → T
    preserves : ∀ s t → relation s t → relation (stepS s) (stepT t)

record RepresentationFactor (X Y : Set) : Set₁ where
  constructor representationFactor
  field
    encode : X → Y
    sourceStep : X → X
    targetStep : Y → Y
    commute : ∀ x → encode (sourceStep x) ≡ targetStep (encode x)

factorPreserves : ∀ {X Y} (F : RepresentationFactor X Y) (x : X) → RepresentationFactor.encode F (RepresentationFactor.sourceStep F x) ≡ RepresentationFactor.targetStep F (RepresentationFactor.encode F x)
factorPreserves F x = RepresentationFactor.commute F x

record CNN64 : Set where
  constructor cnn64
  field code64 : V (Fin 256) 64

cnnToLearnerInput : CNN64 → V (Fin 256) 64
cnnToLearnerInput c = CNN64.code64 c

cnnRepresentationFactor : RepresentationFactor CNN64 (V (Fin 256) 64)
cnnRepresentationFactor = representationFactor cnnToLearnerInput (λ x → x) (λ x → x) (λ x → refl)
