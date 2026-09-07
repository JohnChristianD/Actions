{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SharedNetworkCHAD where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.FirstClassRecurrentCHAD public

------------------------------------------------------------------------
-- One shared network definition.
-- Representation and recurrent execution are built from the same CHAD
-- Nodes. Each Node contains its primal and pullback program together.
------------------------------------------------------------------------

record NetworkPrimitives (X hiddenDim Y : Set) : Set₁ where
  field
    affine : Node X hiddenDim
    layerNorm : Node hiddenDim hiddenDim
    tanhHead : Node hiddenDim hiddenDim
    output : Node hiddenDim Y
    lstm : LSTMNodes X hiddenDim

open NetworkPrimitives

representation : ∀ {X hiddenDim Y : Set}
  → NetworkPrimitives X hiddenDim Y
  → Node X hiddenDim
representation p =
  compose (compose (affine p) (layerNorm p)) (tanhHead p)

actorNetwork : ∀ {X hiddenDim Y : Set}
  → NetworkPrimitives X hiddenDim Y
  → Node X Y
actorNetwork p = compose (representation p) (output p)

lstmNetwork : ∀ {X hiddenDim : Set} {n : Nat}
  → NetworkPrimitives X hiddenDim hiddenDim
  → Vec X n
  → Node (LSTMState hiddenDim) (LSTMState hiddenDim)
lstmNetwork p xs = lstmUnroll xs (NetworkPrimitives.lstm p)

representationForwardBoundary : ∀ {X hiddenDim Y : Set}
  (p : NetworkPrimitives X hiddenDim Y) (x : X)
  → primal (representation p) x ≡
      primal (tanhHead p)
        (primal (layerNorm p) (primal (affine p) x))
representationForwardBoundary p x = refl

actorForwardBoundary : ∀ {X hiddenDim Y : Set}
  (p : NetworkPrimitives X hiddenDim Y) (x : X)
  → primal (actorNetwork p) x ≡
      primal (output p) (primal (representation p) x)
actorForwardBoundary p x = refl

lstmForwardBoundary : ∀ {X hiddenDim : Set} {n : Nat}
  (p : NetworkPrimitives X hiddenDim hiddenDim)
  (xs : Vec X n) (s : LSTMState hiddenDim)
  → primal (lstmNetwork p xs) s ≡ primal (lstmNetwork p xs) s
lstmForwardBoundary p xs s = refl
