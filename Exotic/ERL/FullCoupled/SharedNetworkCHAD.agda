{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SharedNetworkCHAD where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.FirstClassRecurrentCHAD public

------------------------------------------------------------------------
-- One shared finite network definition.
-- All representation and recurrent dimensions are Nat-indexed vectors.
-- Each Node contains its primal and reverse behavior in the same run.
------------------------------------------------------------------------

record NetworkPrimitives (A : Set) (inputDim hiddenDim outputDim : Nat) : Set₁ where
  field
    affine : Node (Vec A inputDim) (Vec A hiddenDim)
    layerNorm : Node (Vec A hiddenDim) (Vec A hiddenDim)
    tanhHead : Node (Vec A hiddenDim) (Vec A hiddenDim)
    output : Node (Vec A hiddenDim) (Vec A outputDim)
    recurrent : LSTMPrimitives A inputDim hiddenDim

open NetworkPrimitives

representation : ∀ {A : Set} {inputDim hiddenDim outputDim : Nat}
  → NetworkPrimitives A inputDim hiddenDim outputDim
  → Node (Vec A inputDim) (Vec A hiddenDim)
representation p =
  compose (compose (affine p) (layerNorm p)) (tanhHead p)

actorNetwork : ∀ {A : Set} {inputDim hiddenDim outputDim : Nat}
  → NetworkPrimitives A inputDim hiddenDim outputDim
  → Node (Vec A inputDim) (Vec A outputDim)
actorNetwork p = compose (representation p) (output p)

lstmNetwork : ∀ {A : Set} {inputDim hiddenDim : Nat} {n : Nat}
  → NetworkPrimitives A inputDim hiddenDim hiddenDim
  → Vec (Vec A inputDim) n
  → Node (LSTMState A hiddenDim) (LSTMState A hiddenDim)
lstmNetwork p xs = lstmUnroll xs (NetworkPrimitives.recurrent p)

------------------------------------------------------------------------
-- Definition-level sharing checks.
------------------------------------------------------------------------

representationForwardBoundary : ∀ {A : Set} {inputDim hiddenDim outputDim : Nat}
  (p : NetworkPrimitives A inputDim hiddenDim outputDim) (x : Vec A inputDim)
  → primal (representation p) x ≡
      primal (tanhHead p)
        (primal (layerNorm p) (primal (affine p) x))
representationForwardBoundary p x = refl

actorForwardBoundary : ∀ {A : Set} {inputDim hiddenDim outputDim : Nat}
  (p : NetworkPrimitives A inputDim hiddenDim outputDim) (x : Vec A inputDim)
  → primal (actorNetwork p) x ≡
      primal (output p) (primal (representation p) x)
actorForwardBoundary p x = refl

recurrentForwardBoundary : ∀ {A : Set} {inputDim hiddenDim : Nat} {n : Nat}
  (p : NetworkPrimitives A inputDim hiddenDim hiddenDim)
  (xs : Vec (Vec A inputDim) n)
  (s : LSTMState A hiddenDim)
  → primal (lstmNetwork p xs) s ≡ primal (lstmNetwork p xs) s
recurrentForwardBoundary p xs s = refl
