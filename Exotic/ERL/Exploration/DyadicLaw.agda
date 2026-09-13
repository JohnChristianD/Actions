{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.DyadicLaw where

open import Data.Product using (_×_; _,_)
open import Exotic.ERL.Exploration.FlatDyadic using
  ( flatWeight-normalized
  ; flatUnit-positive
  ; flatUnit-negative-positive
  ; flatZero-positive
  ; flatUniversal-positive
  )
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
  ; ladderPowerTwo-support
  )

data DyadicLaw : Set where
  lazyWalk : DyadicLaw
  dyadicLadder : DyadicLaw
  flatDyadic : DyadicLaw

law-normalized : DyadicLaw → Set
law-normalized lazyWalk = lazyWeight-sum
law-normalized dyadicLadder = ladderWeight-sum
law-normalized flatDyadic = flatWeight-normalized

law-unit-support : DyadicLaw → Set
law-unit-support lazyWalk = lazyForward-positive × lazyBackward-positive
law-unit-support dyadicLadder = ladderUnit-positive × ladderUnit-negative-positive
law-unit-support flatDyadic = flatUnit-positive × flatUnit-negative-positive

law-zero-support : DyadicLaw → Set
law-zero-support lazyWalk = lazyStay-positive
law-zero-support dyadicLadder = ladderStay-positive
law-zero-support flatDyadic = flatZero-positive

law-power-two-support : DyadicLaw → Set
law-power-two-support lazyWalk = lazyWeight-sum
law-power-two-support dyadicLadder = ladderPowerTwo-support
law-power-two-support flatDyadic = flatUniversal-positive

law-universal-support : DyadicLaw → Set
law-universal-support lazyWalk = lazyWeight-sum
law-universal-support dyadicLadder = ladderWeight-sum
law-universal-support flatDyadic = flatUniversal-positive

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

dyadicLadderPowerTwoSupport : law-power-two-support dyadicLadder
dyadicLadderPowerTwoSupport = ladderPowerTwo-support

flatDyadicNormalized : law-normalized flatDyadic
flatDyadicNormalized = flatWeight-normalized

flatDyadicUnitSupport : law-unit-support flatDyadic
flatDyadicUnitSupport = flatUnit-positive , flatUnit-negative-positive

flatDyadicZeroSupport : law-zero-support flatDyadic
flatDyadicZeroSupport = flatZero-positive

flatDyadicUniversalSupport : law-universal-support flatDyadic
flatDyadicUniversalSupport = flatUniversal-positive
