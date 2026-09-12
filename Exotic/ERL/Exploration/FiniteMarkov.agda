{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.FiniteMarkov where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (Int8; one8; zero8)
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; zero; weight)
open import Exotic.ERL.Exploration.NoisyNetFinite using (perturbScalar; zeroPerturbationExample)

transition : Noise → Int8 → Int8
transition = perturbScalar

selfLoopExample : transition zero one8 ≡ one8
selfLoopExample = zeroPerturbationExample

selfLoopWeight : weight zero ≡ 2
selfLoopWeight = refl

finiteStateCarrier : Set
finiteStateCarrier = Int8
