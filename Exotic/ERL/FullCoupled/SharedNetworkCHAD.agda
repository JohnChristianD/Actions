{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SharedNetworkCHAD where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.FirstClassRecurrentCHAD public

------------------------------------------------------------------------
-- One shared network definition. The same Node carries its primal value
-- and reverse accumulator. The recurrent part is the compositional LSTM
-- node graph, not a separate recurrent primitive slot.
------------------------------------------------------------------------

record NetworkPrimitives (X H Y : Set) : Set₁ where
  field
    affine : Node X H
    layerNorm : Node H H
    tanhHead : Node H H
    output : Node H Y
    lstm : LSTMNodes X H

open NetworkPrimitives

representation : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y → Node X H
representation p =
  compose (compose (affine p) (layerNorm p)) (tanhHead p)

actorNetwork : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y → Node X Y
actorNetwork p = compose (representation p) (output p)

lstmNetwork : ∀ {X H : Set} {n : Nat}
  → NetworkPrimitives X H H → Vec X n
  → Node (LSTMState H) (LSTMState H)
lstmNetwork p xs = lstmUnroll xs (NetworkPrimitives.lstm p)

representationForwardBoundary : ∀ {X H Y : Set}
  (p : NetworkPrimitives X H Y) (x : X) →
  primal (representation p) x ≡
    primal (tanhHead p)
      (primal (layerNorm p) (primal (affine p) x))
representationForwardBoundary p x = refl

actorForwardBoundary : ∀ {X H Y : Set}
  (p : NetworkPrimitives X H Y) (x : X) →
  primal (actorNetwork p) x ≡
    primal (output p) (primal (representation p) x)
actorForwardBoundary p x = refl

gateConstructionBoundary : ∀ {X H : Set}
  (ops : LSTMNodes X H) (g : LSTMGate X H) (x : X) (h : H) →
  primal (gateSigmoid g ops) (x , h) ≡
    primal (LSTMNodes.sigmoidH ops)
      (primal (LSTMGate.layerNorm g)
        (primal (LSTMGate.affine g) (x , h)))
gateConstructionBoundary ops g x h = refl
