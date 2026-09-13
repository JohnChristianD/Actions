{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearner_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (zero8; one8)
open import Exotic.ERL.Exploration.FiniteNoise using (zero)
open import Exotic.ERL.FullCoupled.CanonicalTransformer
open import Exotic.ERL.FullCoupled.CanonicalLearner

canonicalOrderTest :
  canonicalForward (gateParametersOf start) zero
    (token zero8 one8 zero8 zero8)
  ≡
  projection (gateParametersOf start)
    (gate (gateParametersOf start) zero
      (sR2
        (sR1
          (fastfood
            (pyrTopK
              (rope
                (embedding (token zero8 one8 zero8 zero8))))))))
canonicalOrderTest = canonicalOrder
  (gateParametersOf start)
  zero
  (token zero8 one8 zero8 zero8)

scaleFloorTest : dyadicScale ellMin ≡ one8
scaleFloorTest = scaleFloor

f4ZeroTest : f4Step initialZero zero8 ≡ initialZero
f4ZeroTest = f4ZeroWitness

xiCommitTest :
  xi (step start zero zero
    (token one8 zero8 one8 zero8)
    (token zero8 zero8 zero8 zero8)
    one8)
  ≡
  f4Step (xi start)
    (qε 3 (proj₁ (gradientBundle start zero zero
      (token one8 zero8 one8 zero8)
      (token zero8 zero8 zero8 zero8)
      one8)))
xiCommitTest = xiCommit start zero zero
  (token one8 zero8 one8 zero8)
  (token zero8 zero8 zero8 zero8)
  one8

zeroSelfLoopTest :
  step start zero zero
    (token zero8 zero8 zero8 zero8)
    (token zero8 zero8 zero8 zero8)
    zero8
  ≡ start
zeroSelfLoopTest = zeroSelfLoop
