{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.DyadicLaw where

open import Data.Product using (_×_; _,_)
open import Exotic.ERL.Exploration.LazyWalkDyadic using
  ( lazyWeight-sum
  ; lazyStay-positive
  ; lazyForward-positive
  ; lazyBackward-positive
  )
open import Exotic.ERL.Exploration.DyadicLadder using
  ( ladderWeight-sum
  ; ladderStay-positive
  ; ladderUnit-positive
  ; ladderUnit-negative-positive
  )
open import Exotic.ERL.Exploration.DyadicGeometric5 using
  ( geoWeight-sum
  ; geoZero-positive
  ; geoUnit-positive
  ; geoUnit-negative-positive
  )

data DyadicLaw : Set where
  lazyWalk : DyadicLaw
  dyadicLadder : DyadicLaw
  dyadicGeometric5 : DyadicLaw

law-normalized : DyadicLaw → Set
law-normalized lazyWalk = lazyWeight-sum
law-normalized dyadicLadder = ladderWeight-sum
law-normalized dyadicGeometric5 = geoWeight-sum

law-unit-support : DyadicLaw → Set
law-unit-support lazyWalk = lazyForward-positive × lazyBackward-positive
law-unit-support dyadicLadder = ladderUnit-positive × ladderUnit-negative-positive
law-unit-support dyadicGeometric5 = geoUnit-positive × geoUnit-negative-positive

law-zero-support : DyadicLaw → Set
law-zero-support lazyWalk = lazyStay-positive
law-zero-support dyadicLadder = ladderStay-positive
law-zero-support dyadicGeometric5 = geoZero-positive

lazyWalkNormalized : law-normalized lazyWalk
lazyWalkNormalized = lazyWeight-sum

lazyWalkUnitSupport : law-unit-support lazyWalk
lazyWalkUnitSupport = lazyForward-positive , lazyBackward-positive

lazyWalkZeroSupport : law-zero-support lazyWalk
lazyWalkZeroSupport = lazyStay-positive

dyadicLadderNormalized : law-normalized dyadicLadder
dyadicLadderNormalized = ladderWeight-sum

dyadicLadderUnitSupport : law-unit-support dyadicLadder
dyadicLadderUnitSupport = ladderUnit-positive , ladderUnit-negative-positive

dyadicLadderZeroSupport : law-zero-support dyadicLadder
dyadicLadderZeroSupport = ladderStay-positive

dyadicGeometric5Normalized : law-normalized dyadicGeometric5
dyadicGeometric5Normalized = geoWeight-sum

dyadicGeometric5UnitSupport : law-unit-support dyadicGeometric5
dyadicGeometric5UnitSupport = geoUnit-positive , geoUnit-negative-positive

dyadicGeometric5ZeroSupport : law-zero-support dyadicGeometric5
dyadicGeometric5ZeroSupport = geoZero-positive
