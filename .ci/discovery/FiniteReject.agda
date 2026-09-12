{-# OPTIONS --safe #-}

module FiniteReject where

open import Agda.Builtin.Nat using (Nat; zero; suc)

finiteCounterexample : Nat
finiteCounterexample = suc zero
