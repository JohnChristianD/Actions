{-# OPTIONS --safe #-}

module Exotic.ERL.Extraction.Agda2HSMain where

open import Haskell.Prelude
open import Data.Fin using (toℕ)
open import Exotic.efficient_chad.Int8 using (code; one8)
open import Exotic.ERL.Finite.TrueOnlineTD using (exampleFeature; exampleNextFeature; exampleStep; theta)
open import Exotic.ERL.Finite.Int8Vector using (x0)
open import Exotic.ERL.Exploration.FiniteNoise using (pos)
open import Exotic.ERL.Exploration.ComposedLearnerExploration using (composedExploreStep)

learnerExampleCode : Nat
learnerExampleCode = toℕ (code (x0 (theta exampleStep)))

composedExampleCode : Nat
composedExampleCode =
  toℕ
    (code
      (x0
        (theta
          (composedExploreStep
            pos
            one8
            exampleFeature
            exampleNextFeature
            exampleStep))))

{-# COMPILE AGDA2HS learnerExampleCode #-}
{-# COMPILE AGDA2HS composedExampleCode #-}
