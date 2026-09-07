{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SharedNetworkCHAD where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.FirstClassRecurrentCHAD public

------------------------------------------------------------------------
-- One shared network definition.  The same Node carries its primal value
-- and reverse accumulator, while the recurrent transition is imported from
-- the first-class compositional LSTM/GRU construction.
------------------------------------------------------------------------

record NetworkPrimitives (X H Y : Set) : Set₁ where
  field
    affine : Node X H
    layerNorm : Node H H
    tanhHead : Node H H
    output : Node H Y
    lstm : LSTMCellNodes X H
    gru : GRUCellNodes X H

open NetworkPrimitives

representation : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y → Node X H
representation p =
  compose
    (compose (affine p) (layerNorm p))
    (tanhHead p)

actorNetwork : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y → Node X Y
actorNetwork p = compose (representation p) (output p)

lstmNetwork : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y
  → Vec X 0
  → Node (LSTMState H) (LSTMState H)
lstmNetwork p xs = lstmUnroll xs (lstm p)

gruNetwork : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y
  → Vec X 0
  → Node (GRUState H) (GRUState H)
gruNetwork p xs = gruUnroll xs (gru p)

------------------------------------------------------------------------
-- Definition-level sharing checks.  These are reflexive because the
-- forward expression is literally the primal projection of the Node whose
-- reverse expression is simultaneously carried by the same `run`.
------------------------------------------------------------------------

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
  (ops : LSTMCellNodes X H) (g : LSTMGateNodes X H) (x : X) (h : H) →
  primal (gateSigmoid g ops) (x , h) ≡
    primal (LSTMCellNodes.sigmoidH ops)
      (primal (LSTMGateNodes.layerNorm g)
        (primal (LSTMGateNodes.affine g) (x , h)))
gateConstructionBoundary ops g x h = refl
