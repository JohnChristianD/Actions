{-# OPTIONS --safe #-}

module Exotic.ERL.Extraction.Agda2HSMain where

open import Haskell.Prelude
open import Data.Fin using (toℕ)
open import Exotic.efficient_chad.Int8 using (code)
open import Exotic.ERL.Finite.TrueOnlineTD using (exampleStep; theta)
open import Exotic.ERL.Finite.Int8Vector using (x0)

learnerExampleCode : Nat
learnerExampleCode = toℕ (code (x0 (theta exampleStep)))

{-# COMPILE AGDA2HS learnerExampleCode #-}
