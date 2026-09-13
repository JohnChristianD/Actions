{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.DyadicGeometric5 where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)

data GeometricOutcome : Set where
  geoZero : GeometricOutcome
  geoP1 : GeometricOutcome
  geoN1 : GeometricOutcome
  geoP2 : GeometricOutcome
  geoN2 : GeometricOutcome
  geoP3 : GeometricOutcome
  geoN3 : GeometricOutcome
  geoP4 : GeometricOutcome
  geoN4 : GeometricOutcome
  geoP5 : GeometricOutcome
  geoN5 : GeometricOutcome

geoWeight : GeometricOutcome → ℕ
geoWeight geoZero = 66
geoWeight geoP1 = 16
geoWeight geoN1 = 16
geoWeight geoP2 = 8
geoWeight geoN2 = 8
geoWeight geoP3 = 4
geoWeight geoN3 = 4
geoWeight geoP4 = 2
geoWeight geoN4 = 2
geoWeight geoP5 = 1
geoWeight geoN5 = 1

geoDenominator : ℕ
geoDenominator = 128

geoWeight-sum :
  geoWeight geoZero
  + geoWeight geoP1 + geoWeight geoN1
  + geoWeight geoP2 + geoWeight geoN2
  + geoWeight geoP3 + geoWeight geoN3
  + geoWeight geoP4 + geoWeight geoN4
  + geoWeight geoP5 + geoWeight geoN5
  ≡ geoDenominator
geoWeight-sum = refl

geoZero-positive : geoWeight geoZero ≡ 66
geoZero-positive = refl

geoUnit-positive : geoWeight geoP1 ≡ 16
geoUnit-positive = refl

geoUnit-negative-positive : geoWeight geoN1 ≡ 16
geoUnit-negative-positive = refl

geoRadius1-halves : geoWeight geoP1 ≡ geoWeight geoP2 * 2
geoRadius1-halves = refl

geoRadius2-halves : geoWeight geoP2 ≡ geoWeight geoP3 * 2
geoRadius2-halves = refl

geoRadius3-halves : geoWeight geoP3 ≡ geoWeight geoP4 * 2
geoRadius3-halves = refl

geoRadius4-halves : geoWeight geoP4 ≡ geoWeight geoP5 * 2
geoRadius4-halves = refl

geoSupport-zero-unit :
  geoWeight geoZero ≡ 66 × geoWeight geoP1 ≡ 16 × geoWeight geoN1 ≡ 16
geoSupport-zero-unit = refl , refl , refl
