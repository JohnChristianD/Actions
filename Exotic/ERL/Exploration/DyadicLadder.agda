{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.DyadicLadder where

open import Data.Nat using (ℕ)
open import Agda.Builtin.Equality using (_≡_; refl)

data LadderOutcome : Set where
  ladderStay : LadderOutcome
  ladderP1 : LadderOutcome
  ladderN1 : LadderOutcome
  ladderP2 : LadderOutcome
  ladderN2 : LadderOutcome
  ladderP4 : LadderOutcome
  ladderN4 : LadderOutcome
  ladderP8 : LadderOutcome
  ladderN8 : LadderOutcome
  ladderP16 : LadderOutcome
  ladderN16 : LadderOutcome
  ladderP32 : LadderOutcome
  ladderN32 : LadderOutcome
  ladderP64 : LadderOutcome
  ladderN64 : LadderOutcome
  ladderP128 : LadderOutcome
  ladderN128 : LadderOutcome

ladderWeight : LadderOutcome → ℕ
ladderWeight ladderStay = 16
ladderWeight _ = 1

ladderDenominator : ℕ
ladderDenominator = 32

ladderWeight-sum :
  ladderWeight ladderStay
  + ladderWeight ladderP1 + ladderWeight ladderN1
  + ladderWeight ladderP2 + ladderWeight ladderN2
  + ladderWeight ladderP4 + ladderWeight ladderN4
  + ladderWeight ladderP8 + ladderWeight ladderN8
  + ladderWeight ladderP16 + ladderWeight ladderN16
  + ladderWeight ladderP32 + ladderWeight ladderN32
  + ladderWeight ladderP64 + ladderWeight ladderN64
  + ladderWeight ladderP128 + ladderWeight ladderN128
  ≡ ladderDenominator
ladderWeight-sum = refl

ladderStay-positive : ladderWeight ladderStay ≡ 16
ladderStay-positive = refl

ladderUnit-positive : ladderWeight ladderP1 ≡ 1
ladderUnit-positive = refl

ladderUnit-negative-positive : ladderWeight ladderN1 ≡ 1
ladderUnit-negative-positive = refl

ladderPowerTwo-support :
  ladderWeight ladderP2 ≡ 1 × ladderWeight ladderN2 ≡ 1
ladderPowerTwo-support = refl , refl
