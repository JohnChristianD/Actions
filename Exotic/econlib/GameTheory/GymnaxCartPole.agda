{-# OPTIONS --safe #-}
module Exotic.econlib.GameTheory.GymnaxCartPole where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Provenance: gymnax classic_control / CartPole-v1.
-- Continuous physics is represented by an explicit finite transition table.
-- The theorem boundary is exact for that finite table and makes the
-- discretisation explicit instead of pretending modular Int8 arithmetic is
-- the original real-valued CartPole integrator.

data Action : Set where
  left right : Action

data Position : Set where
  p0 p1 p2 p3 p4 : Position

data Velocity : Set where
  v0 v1 v2 : Velocity

data Pole : Set where
  q0 q1 q2 q3 q4 : Pole

record CartPoleState : Set where
  constructor cartPoleState
  field
    x : Position
    v : Velocity
    angle : Pole

record CartPoleKernel : Set where
  constructor cartPoleKernel
  field
    transition : CartPoleState → Action → CartPoleState
    reward : CartPoleState → Action → Nat

step : CartPoleKernel → CartPoleState → Action → CartPoleState
step K s a = CartPoleKernel.transition K s a

rewardOf : CartPoleKernel → CartPoleState → Action → Nat
rewardOf K s a = CartPoleKernel.reward K s a
