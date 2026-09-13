{-# OPTIONS --safe #-}

module Exotic.ERL.Exploration.DMCPDistribution where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin as F using (Fin)
open import Data.Nat using (Nat; zero; suc; _+_)

Scale : Set
Scale = Fin 4

dyadicDenominator : Nat
dyadicDenominator = 4

dmcpMass : Scale → Nat
dmcpMass _ = suc zero

dmcpMassTotal :
  dmcpMass F.zero +
  dmcpMass (F.suc F.zero) +
  dmcpMass (F.suc (F.suc F.zero)) +
  dmcpMass (F.suc (F.suc (F.suc F.zero)))
  ≡ dyadicDenominator
dmcpMassTotal = refl

record DyadicScaleDistribution : Set where
  constructor dyadicScaleDistribution
  field
    mass : Scale → Nat
    total :
      mass F.zero +
      mass (F.suc F.zero) +
      mass (F.suc (F.suc F.zero)) +
      mass (F.suc (F.suc (F.suc F.zero)))
      ≡ dyadicDenominator

DMCP : DyadicScaleDistribution
DMCP = dyadicScaleDistribution dmcpMass dmcpMassTotal

dmcpIsDistribution : DyadicScaleDistribution.total DMCP ≡ dyadicDenominator
dmcpIsDistribution = refl
