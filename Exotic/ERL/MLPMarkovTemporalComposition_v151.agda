{-# OPTIONS --safe #-}
module Exotic.ERL.MLPMarkovTemporalComposition_v151 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl; sym; cong; trans)

------------------------------------------------------------------------
-- Stateful MLP as a finite Markov transition system.
-- The neural map is pure; memory lives in an explicit finite state carrier.
------------------------------------------------------------------------

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

appendV : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
appendV [] ys = ys
appendV (x ∷ xs) ys = x ∷ appendV xs ys

record Monoid : Set₁ where
  field
    Carrier : Set
    neutral : Carrier
    _∙_ : Carrier → Carrier → Carrier
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    neutralL : ∀ x → neutral ∙ x ≡ x
    neutralR : ∀ x → x ∙ neutral ≡ x

open Monoid

record StepResult (H Y : Set) : Set where
  field
    state : H
    output : Y

open StepResult

record StatefulMLP (X H Y : Set) (M : Monoid) : Set₁ where
  field
    transition : H → X → H
    forward : H → X → Y

stepMLP : ∀ {X H Y} {M : Monoid} →
  StatefulMLP X H Y M → H → X → StepResult H Y
stepMLP net h x = record
  { state = StatefulMLP.transition net h x
  ; output = StatefulMLP.forward net h x
  }

record RunResult (H C : Set) : Set where
  field
    finalState : H
    summary : C

open RunResult

runChunk : ∀ {X H Y} (M : Monoid) →
  StatefulMLP X H Y M → H → Vec X zero → RunResult H (Carrier M)
runChunk M net h [] = record
  { finalState = h
  ; summary = neutral M
  }

runChunkS : ∀ {X H Y} (M : Monoid) →
  StatefulMLP X H Y M → H → ∀ {n} → Vec X (suc n) → RunResult H (Carrier M)
runChunkS M net h (x ∷ xs) =
  let r = stepMLP net h x
      rr = runChunkS M net (StepResult.state r) xs
  in record
    { finalState = RunResult.finalState rr
    ; summary = Monoid._∙_ M (StepResult.output r) (RunResult.summary rr)
    }

run : ∀ {X H Y n} (M : Monoid) →
  StatefulMLP X H Y M → H → Vec X n → RunResult H (Carrier M)
run M net h [] = runChunk M net h []
run M net h (x ∷ xs) = runChunkS M net h (x ∷ xs)

------------------------------------------------------------------------
-- Emergent finite Markov property.
-- Once the final state of the first chunk is retained, the future chunk is
-- independent of the internal history of the first chunk.
------------------------------------------------------------------------

markovAppend : ∀ {X H Y m n} (M : Monoid)
  (net : StatefulMLP X H Y M)
  (h : H)
  (xs : Vec X m)
  (ys : Vec X n) →
  run M net h (appendV xs ys) ≡
  let r = run M net h xs
      t = run M net (RunResult.finalState r) ys
  in record
    { finalState = RunResult.finalState t
    ; summary = Monoid._∙_ M (RunResult.summary r) (RunResult.summary t)
    }
markovAppend M net h [] ys =
  sym (Monoid.neutralL M (RunResult.summary (run M net h ys)))
markovAppend M net h (x ∷ xs) ys =
  let r = stepMLP net h x
      tailProof = markovAppend M net (StepResult.state r) xs ys
  in trans
    (cong
      (λ q → record
        { finalState = RunResult.finalState q
        ; summary = Monoid._∙_ M (StepResult.output r) (RunResult.summary q)
        })
      tailProof)
    (sym (Monoid.assoc M
      (StepResult.output r)
      (RunResult.summary (run M net (StepResult.state r) xs))
      (RunResult.summary
        (run M net
          (RunResult.finalState (run M net (StepResult.state r) xs))
          ys))))

------------------------------------------------------------------------
-- Temporal normal form: execute the first chunk, retain only Markov state and
-- accumulated summary, then execute the second chunk.
------------------------------------------------------------------------

markovTemporalNormalForm : ∀ {X H Y m n} (M : Monoid)
  (net : StatefulMLP X H Y M)
  (h : H)
  (xs : Vec X m)
  (ys : Vec X n) →
  run M net h (appendV xs ys) ≡
  let r = run M net h xs
      t = run M net (RunResult.finalState r) ys
  in record
    { finalState = RunResult.finalState t
    ; summary = Monoid._∙_ M (RunResult.summary r) (RunResult.summary t)
    }
markovTemporalNormalForm = markovAppend
