{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearner_test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.efficient_chad.Int8 using (zero8; one8)
open import Exotic.ERL.FullCoupled.FiniteVJP
open import Exotic.ERL.FullCoupled.CanonicalTransformer
open import Exotic.ERL.FullCoupled.CanonicalLearner

canonicalOrderTest :
  canonicalForward initialGate (token zero8 one8 zero8 zero8) ≡
  projection
    (gate initialGate
      (sR2
        (sR1
          (fastfood
            (pyrTopK
              (rope
                (embedding (token zero8 one8 zero8 zero8))))))))
canonicalOrderTest = canonicalOrder initialGate (token zero8 one8 zero8 zero8)

scaleFloorTest : dyadicScale ellMin ≡ one8
scaleFloorTest = scaleFloor

f4ZeroTest : f4Step initialF4 zero8 ≡ initialF4
f4ZeroTest = f4ZeroLaw initialF4

xiCommitTest :
  xi (step start (token one8 zero8 one8 zero8) (token zero8 zero8 zero8 zero8) one8)
  ≡
  f4Step (xi start)
    (qε 3 (proj₁ (gradientBundle start
      (token one8 zero8 one8 zero8)
      (token zero8 zero8 zero8 zero8)
      one8)))
xiCommitTest = xiCommit start
  (token one8 zero8 one8 zero8)
  (token zero8 zero8 zero8 zero8)
  one8
