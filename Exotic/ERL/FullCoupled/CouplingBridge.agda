{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CouplingBridge where

open import Exotic.ERL.Finite.TrueOnlineTD using (TrueOnlineState)
open import Exotic.ERL.FullCoupled.F4IntKernel using (F4State)

Coupled : Set
Coupled = TrueOnlineState
