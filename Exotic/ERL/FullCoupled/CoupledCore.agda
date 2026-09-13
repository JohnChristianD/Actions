{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CoupledCore where

open import Data.Product using (_×_; _,_)
open import Exotic.ERL.Finite.TrueOnlineTD using (TrueOnlineState)
open import Exotic.ERL.FullCoupled.F4IntKernel using (F4State)

joint : F4State -> TrueOnlineState -> F4State × TrueOnlineState
joint f c = f , c
