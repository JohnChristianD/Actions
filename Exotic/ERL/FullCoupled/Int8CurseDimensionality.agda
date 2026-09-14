{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.Int8CurseDimensionality where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; _+_; _*_; _^_)

------------------------------------------------------------------------
-- Finite-state curse of dimensionality.
--
-- An Int8 coordinate has 256 values. A d-coordinate hidden vector therefore
-- has 256^d possible states. If k independent Int8 noise coordinates are
-- included in the Markov state, the joint carrier has 256^(d+k) states.
-- Keeping T+1 complete recurrent states in a trajectory gives
-- 256^((d+k)*(T+1)) possible trajectories.
--
-- The recurrent window length does NOT force the Markov carrier itself to
-- grow: with a fixed recurrent state, an unbounded horizon is an unbounded
-- sequence over the same finite carrier. Thus recurrence avoids a temporal
-- blow-up of the carrier, but does not remove the exponential dependence on
-- vector dimension or persistent noise dimension.
------------------------------------------------------------------------

int8Cardinality : ℕ
int8Cardinality = 256

hiddenCardinality : ℕ → ℕ
hiddenCardinality d = int8Cardinality ^ d

jointCardinality : ℕ → ℕ → ℕ
jointCardinality d k = int8Cardinality ^ (d + k)

trajectoryCardinality : ℕ → ℕ → ℕ → ℕ
trajectoryCardinality d k t = int8Cardinality ^ ((d + k) * (t + 1))

hiddenCardinality-zero : hiddenCardinality 0 ≡ 1
hiddenCardinality-zero = refl

jointCardinality-zero-noise :
  ∀ d → jointCardinality d 0 ≡ hiddenCardinality d
jointCardinality-zero-noise d = refl

trajectoryCardinality-zero-window :
  ∀ d k → trajectoryCardinality d k 0 ≡ jointCardinality d k
trajectoryCardinality-zero-window d k = refl

------------------------------------------------------------------------
-- Noisy-Net exploration support is a carrier extension only when its noise
-- variables are persistent state. If noise is sampled exogenously at each
-- step, it belongs to the transition kernel instead and does not multiply
-- the persistent carrier cardinality.
------------------------------------------------------------------------

record NoiseAccounting : Set where
  constructor noiseAccounting
  field
    persistentNoiseDimensions : ℕ
    sampledNoiseDimensions : ℕ

persistentCarrierCardinality : ℕ → NoiseAccounting → ℕ
persistentCarrierCardinality d n =
  int8Cardinality ^ (d + NoiseAccounting.persistentNoiseDimensions n)

sampledNoiseCarrierCardinality : ℕ → NoiseAccounting → ℕ
sampledNoiseCarrierCardinality d n = int8Cardinality ^ d

persistentNoise-expansion :
  ∀ d n →
  persistentCarrierCardinality d n ≡
  int8Cardinality ^ (d + NoiseAccounting.persistentNoiseDimensions n)
persistentNoise-expansion d n = refl

sampledNoise-does-not-expand-carrier :
  ∀ d n → sampledNoiseCarrierCardinality d n ≡ int8Cardinality ^ d
sampledNoise-does-not-expand-carrier d n = refl
