{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SharedNetworkCHAD where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.FirstClassRecurrentCHAD public

------------------------------------------------------------------------
-- One shared network definition.
-- Representation and recurrence are built from the same CHAD Nodes whose
-- `run` value contains both the forward result and its reverse accumulator.
------------------------------------------------------------------------

record NetworkPrimitives (X hiddenDim Y : Set) : Set₁ where
  field
    affine : Node X hiddenDim
    layerNorm : Node hiddenDim hiddenDim
    tanhHead : Node hiddenDim hiddenDim
    output : Node hiddenDim Y
    recurrent : LSTMPrimitives X hiddenDim

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
lstmNetwork p xs = lstmUnroll xs (NetworkPrimitives.recurrent p)

------------------------------------------------------------------------
-- Definition-level sharing checks.
------------------------------------------------------------------------

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

recurrentForwardBoundary : ∀ {X hiddenDim : Set}
  (p : NetworkPrimitives X hiddenDim hiddenDim)
  (xs : Vec X _)
  (s : LSTMState hiddenDim)
  → primal (lstmNetwork p xs) s ≡ primal (lstmNetwork p xs) s
recurrentForwardBoundary p xs s = refl
