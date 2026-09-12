{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.NoisyNetFinite where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8OfNat
  ; zero8
  ; one8
  )
open import Exotic.ERL.Finite.Int8Vector using
  ( Int8Vector4
  ; vec4
  ; x0
  ; x1
  ; x2
  ; x3
  )
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; neg; zero; pos)

noiseDelta : Noise → Int8
noiseDelta neg = int8OfNat 255
noiseDelta zero = zero8
noiseDelta pos = one8

perturbScalar : Noise → Int8 → Int8
perturbScalar n x = int8Add x (noiseDelta n)

perturbVector4 : Noise → Int8Vector4 → Int8Vector4
perturbVector4 n v = vec4
  (perturbScalar n (x0 v))
  (perturbScalar n (x1 v))
  (perturbScalar n (x2 v))
  (perturbScalar n (x3 v))

zeroPerturbationExample : perturbScalar zero one8 ≡ one8
zeroPerturbationExample = refl
