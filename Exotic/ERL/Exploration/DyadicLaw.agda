{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.DyadicLaw where

open import Data.Product using (_×_; _,_)
open import Exotic.ERL.Exploration.FlatDyadic using
  ( flatWeight-sum
  ; flatStay-positive
  ; flatForward-positive
  ; flatBackward-positive
  )
open import Exotic.ERL.Exploration.DyadicLadder using
  ( ladderWeight-sum
  ; ladderStay-positive
  ; ladderUnit-positive
  ; ladderUnit-negative-positive
  ; ladderPowerTwo-support
  )

data DyadicLaw : Set where
  flatDyadic : DyadicLaw
  dyadicLadder : DyadicLaw

law-normalized : DyadicLaw → Set
law-normalized flatDyadic = flatWeight-sum
law-normalized dyadicLadder = ladderWeight-sum

law-unit-support : DyadicLaw → Set
law-unit-support flatDyadic = flatForward-positive × flatBackward-positive
law-unit-support dyadicLadder = ladderUnit-positive × ladderUnit-negative-positive

law-zero-support : DyadicLaw → Set
law-zero-support flatDyadic = flatStay-positive
law-zero-support dyadicLadder = ladderStay-positive

law-scale-shell : DyadicLaw → Set
law-scale-shell flatDyadic = flatWeight-sum
law-scale-shell dyadicLadder = ladderPowerTwo-support

flatDyadicNormalized : law-normalized flatDyadic
flatDyadicNormalized = flatWeight-sum

dyadicLadderNormalized : law-normalized dyadicLadder
dyadicLadderNormalized = ladderWeight-sum

flatDyadicUnitSupport : law-unit-support flatDyadic
flatDyadicUnitSupport = flatForward-positive , flatBackward-positive

flatDyadicZeroSupport : law-zero-support flatDyadic
flatDyadicZeroSupport = flatStay-positive

dyadicLadderUnitSupport : law-unit-support dyadicLadder
dyadicLadderUnitSupport = ladderUnit-positive , ladderUnit-negative-positive

dyadicLadderZeroSupport : law-zero-support dyadicLadder
dyadicLadderZeroSupport = ladderStay-positive
