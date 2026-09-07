{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SharedNetworkCHAD where

open import Agda.Builtin.Equality using (_≡_; refl)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

record Node (A B : Set) : Set₁ where
  field
    primal : A → B
    pullback : A → B → A

open Node

identity : ∀ {A : Set} → Node A A
identity = record { primal = λ x → x ; pullback = λ _ dy → dy }

compose : ∀ {A B C : Set} → Node A B → Node B C → Node A C
compose f g = record
  { primal = λ x → primal g (primal f x)
  ; pullback = λ x dz → pullback f x (pullback g (primal f x) dz)
  }

boundary : ∀ {A B : Set} (n : Node A B) x → primal n x ≡ primal n x
boundary n x = refl

record LSTMState (H : Set) : Set where
  constructor lstm-state
  field
    hidden : H
    cell : H

record GRUState (H : Set) : Set where
  constructor gru-state
  field
    hidden : H

record NetworkPrimitives (X H Y : Set) : Set₁ where
  field
    affine : Node X H
    layerNorm : Node H H
    tanhBlock : Node H H
    sigmoidBlock : Node H H
    output : Node H Y
    lstmStep : Node (X × LSTMState H) (LSTMState H)
    gruStep : Node (X × GRUState H) (GRUState H)

open NetworkPrimitives

representation : ∀ {X H Y : Set} → NetworkPrimitives X H Y → Node X H
representation p =
  compose
    (compose (affine p) (layerNorm p))
    (tanhBlock p)

actorNetwork : ∀ {X H Y : Set} → NetworkPrimitives X H Y → Node X Y
actorNetwork p = compose (representation p) (output p)

lstmNetworkStep : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y
  → Node (X × LSTMState H) (LSTMState H)
lstmNetworkStep p = lstmStep p

gruNetworkStep : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y
  → Node (X × GRUState H) (GRUState H)
gruNetworkStep p = gruStep p

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
