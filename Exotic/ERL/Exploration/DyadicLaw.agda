{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.DyadicLaw where

open import Data.Product using (_×_; _,_)
open import Exotic.ERL.Exploration.FlatDyadic using
  ( flatWeight-sum
  ; flatStay-positive
  ; flatForward-positive
  ; flatBackward-positive
  )

data DyadicLaw : Set where
  flatDyadic : DyadicLaw

law-normalized : DyadicLaw → Set
law-normalized flatDyadic = flatWeight-sum

law-unit-support : DyadicLaw → Set
law-unit-support flatDyadic = flatForward-positive × flatBackward-positive

law-zero-support : DyadicLaw → Set
law-zero-support flatDyadic = flatStay-positive

flatDyadicNormalized : law-normalized flatDyadic
flatDyadicNormalized = flatWeight-sum

flatDyadicUnitSupport : law-unit-support flatDyadic
flatDyadicUnitSupport = flatForward-positive , flatBackward-positive

flatDyadicZeroSupport : law-zero-support flatDyadic
flatDyadicZeroSupport = flatStay-positive
