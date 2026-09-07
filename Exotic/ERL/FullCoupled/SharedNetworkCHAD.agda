{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SharedNetworkCHAD where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 5 _∷_
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

data NodeList (A : Set₁) : Set₁ where
  [] : NodeList A
  _∷_ : A → NodeList A → NodeList A

------------------------------------------------------------------------
-- Efficient-CHAD node: one function simultaneously produces the primal
-- value and its reverse accumulator.  There are no parallel primal/VJP
-- definitions to drift apart.
------------------------------------------------------------------------

record Node (A B : Set) : Set₁ where
  field
    run : A → Σ B (λ _ → B → A)

open Node

primal : ∀ {A B : Set} → Node A B → A → B
primal n x = fst (run n x)

pullback : ∀ {A B : Set} → Node A B → A → B → A
pullback n x dy = snd (run n x) dy

identity : ∀ {A : Set} → Node A A
identity = record
  { run = λ x → x , (λ dy → dy)
  }

compose : ∀ {A B C : Set} → Node A B → Node B C → Node A C
compose f g = record
  { run = λ x →
      let fx = run f x
          gx = run g (fst fx)
      in fst gx , (λ dz → snd fx (snd gx dz))
  }

------------------------------------------------------------------------
-- Finite vector node.  Mapping a single scalar CHAD node constructs both
-- vector primal evaluation and vector reverse accumulation structurally.
------------------------------------------------------------------------

mapVec : ∀ {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

mapVecBack : ∀ {A B : Set} {n : Nat}
  → Node A B → Vec A n → Vec B n → Vec A n
mapVecBack node [] [] = []
mapVecBack node (x ∷ xs) (dy ∷ dys) =
  pullback node x dy ∷ mapVecBack node xs dys

mapNode : ∀ {A B : Set} {n : Nat} → Node A B → Node (Vec A n) (Vec B n)
mapNode node = record
  { run = λ xs → mapVec (primal node) xs , (λ dys → mapVecBack node xs dys)
  }

mapNodeForwardBoundary : ∀ {A B : Set} {n : Nat}
  (node : Node A B) xs →
  primal (mapNode node) xs ≡ mapVec (primal node) xs
mapNodeForwardBoundary node xs = refl

mapNodeReverseBoundary : ∀ {A B : Set} {n : Nat}
  (node : Node A B) xs dy →
  pullback (mapNode node) xs dy ≡ mapVecBack node xs dy
mapNodeReverseBoundary node xs dy = refl

------------------------------------------------------------------------
-- Finite state passing.  Repeated composition of the same Node is the
-- recurrent reverse pass, with finite fuel guaranteeing totality.
------------------------------------------------------------------------

iterate : ∀ {A : Set} → Nat → Node A A → Node A A
iterate zero n = identity
iterate (suc k) n = compose n (iterate k n)

------------------------------------------------------------------------
-- Functional recurrent-state shapes.
------------------------------------------------------------------------

record LSTMState (H : Set) : Set where
  constructor lstm-state
  field
    hidden : H
    cell : H

record GRUState (H : Set) : Set where
  constructor gru-state
  field
    hidden : H

------------------------------------------------------------------------
-- A recurrent transition is itself one paired function.  The equations of
-- the concrete LSTM/GRU layer therefore live inside the transition's run
-- definition; any scalar/vector primitives they call use the same Node
-- interface.
------------------------------------------------------------------------

record RecurrentPrimitives (X H : Set) : Set₁ where
  field
    lstmRun : (X × LSTMState H) →
      Σ (LSTMState H) (λ _ → LSTMState H → X × LSTMState H)
    gruRun : (X × GRUState H) →
      Σ (GRUState H) (λ _ → GRUState H → X × GRUState H)

open RecurrentPrimitives

lstmStepFromRun : ∀ {X H : Set}
  → RecurrentPrimitives X H
  → Node (X × LSTMState H) (LSTMState H)
lstmStepFromRun p = record { run = lstmRun p }

gruStepFromRun : ∀ {X H : Set}
  → RecurrentPrimitives X H
  → Node (X × GRUState H) (GRUState H)
gruStepFromRun p = record { run = gruRun p }

lstmUnroll : ∀ {X H : Set}
  → Nat
  → Node (X × LSTMState H) (X × LSTMState H)
  → Node (X × LSTMState H) (X × LSTMState H)
lstmUnroll k step = iterate k step

gruUnroll : ∀ {X H : Set}
  → Nat
  → Node (X × GRUState H) (X × GRUState H)
  → Node (X × GRUState H) (X × GRUState H)
gruUnroll k step = iterate k step

------------------------------------------------------------------------
-- Representation/actor composition contains no mandatory standalone tanh.
-- A tanh head is an explicit Node only when that architecture selects one.
------------------------------------------------------------------------

record NetworkPrimitives (X H Y : Set) : Set₁ where
  field
    affine : Node X H
    layerNorm : Node H H
    output : Node H Y
    recurrent : RecurrentPrimitives X H

open NetworkPrimitives

representation : ∀ {X H Y : Set} → NetworkPrimitives X H Y → Node X H
representation p = compose (affine p) (layerNorm p)

actorNetwork : ∀ {X H Y : Set} → NetworkPrimitives X H Y → Node X Y
actorNetwork p = compose (representation p) (output p)

lstmNetworkStep : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y
  → Node (X × LSTMState H) (LSTMState H)
lstmNetworkStep p = lstmStepFromRun (recurrent p)

gruNetworkStep : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y
  → Node (X × GRUState H) (GRUState H)
gruNetworkStep p = gruStepFromRun (recurrent p)

------------------------------------------------------------------------
-- Definition-level sharing checks.
------------------------------------------------------------------------

representationForwardBoundary : ∀ {X H Y : Set}
  (p : NetworkPrimitives X H Y) x →
  primal (representation p) x ≡
    primal (layerNorm p) (primal (affine p) x)
representationForwardBoundary p x = refl

actorForwardBoundary : ∀ {X H Y : Set}
  (p : NetworkPrimitives X H Y) x →
  primal (actorNetwork p) x ≡
    primal (output p) (primal (representation p) x)
actorForwardBoundary p x = refl
