{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SharedNetworkCHAD where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- One shared functional forward/reverse program.
--
-- A Node carries its primal evaluator and its Efficient-CHAD pullback in
-- the same definition.  Composition constructs both together; there is no
-- separate Jacobian/VJP theorem surface.
------------------------------------------------------------------------

record Node (A B : Set) : Set₁ where
  field
    primal : A → B
    pullback : A → B → A

open Node

identity : ∀ {A : Set} → Node A A
identity = record
  { primal = λ x → x
  ; pullback = λ _ dy → dy
  }

compose : ∀ {A B C : Set} → Node A B → Node B C → Node A C
compose f g = record
  { primal = λ x → primal g (primal f x)
  ; pullback = λ x dz → pullback f x (pullback g (primal f x) dz)
  }

boundary : ∀ {A B : Set} (n : Node A B) x → primal n x ≡ primal n x
boundary n x = refl

------------------------------------------------------------------------
-- Functional recurrent-state shape.
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
-- Primitive blocks are Nodes.  Their reverse clauses are the only local
-- primitive differentiation interface; network differentiation is then
-- obtained definitionally by compose.
------------------------------------------------------------------------

record NetworkPrimitives (X H Y : Set) : Set₁ where
  field
    affine : Node X H
    layerNorm : Node H H
    tanhBlock : Node H H
    sigmoidBlock : Node H H
    output : Node H Y
    lstmStep : Node (X Σ LSTMState H) (LSTMState H)
    gruStep : Node (X Σ GRUState H) (GRUState H)

open NetworkPrimitives

representation : ∀ {X H Y : Set} → NetworkPrimitives X H Y → Node X H
representation p =
  compose
    (compose (affine p) (layerNorm p))
    (tanhBlock p)

actorNetwork : ∀ {X H Y : Set} → NetworkPrimitives X H Y → Node X Y
actorNetwork p = compose (representation p) (output p)

------------------------------------------------------------------------
-- Recurrent layers already contain their own activation structure.
-- A tanhBlock is therefore a separate representation choice rather than a
-- requirement for LSTM/GRU feature completeness.
------------------------------------------------------------------------

lstmNetworkStep : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y
  → Node (X Σ LSTMState H) (LSTMState H)
lstmNetworkStep p = lstmStep p

gruNetworkStep : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y
  → Node (X Σ GRUState H) (GRUState H)
gruNetworkStep p = gruStep p

------------------------------------------------------------------------
-- Definition-level sharing checks.
------------------------------------------------------------------------

representationForwardBoundary : ∀ {X H Y : Set}
  (p : NetworkPrimitives X H Y) x →
  primal (representation p) x ≡
    primal (tanhBlock p) (primal (layerNorm p) (primal (affine p) x))
representationForwardBoundary p x = refl

actorForwardBoundary : ∀ {X H Y : Set}
  (p : NetworkPrimitives X H Y) x →
  primal (actorNetwork p) x ≡
    primal (output p) (primal (representation p) x)
actorForwardBoundary p x = refl
