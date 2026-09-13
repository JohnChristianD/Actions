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
  ; ladderPowerTwo-support
  )
open import Exotic.ERL.Exploration.FlatDyadic using
  ( flatWeight-normalized
  ; flatUnit-positive
  ; flatUnit-negative-positive
  ; flatZero-positive
  ; flatPowerTwo-support
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
law-unit-support lazyWalk =
  lazyForward-positive × lazyBackward-positive
law-unit-support dyadicLadder =
  ladderUnit-positive × ladderUnit-negative-positive
law-unit-support flatDyadic =
  flatUnit-positive × flatUnit-negative-positive

law-zero-support : DyadicLaw → Set
law-zero-support lazyWalk = lazyStay-positive
law-zero-support dyadicLadder = ladderStay-positive
law-zero-support flatDyadic = flatZero-positive

law-ladder-multiscale : DyadicLaw → Set
law-ladder-multiscale lazyWalk = lazyWeight-sum
law-ladder-multiscale dyadicLadder = ladderPowerTwo-support
law-ladder-multiscale flatDyadic = flatPowerTwo-support

lazyWalkNormalized : law-normalized lazyWalk
lazyWalkNormalized = lazyWeight-sum

dyadicLadderNormalized : law-normalized dyadicLadder
dyadicLadderNormalized = ladderWeight-sum

flatDyadicNormalized : law-normalized flatDyadic
flatDyadicNormalized = flatWeight-normalized
