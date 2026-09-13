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

data DyadicLaw : Set where
  flatDyadic : DyadicLaw

law-normalized : DyadicLaw → Set
law-normalized flatDyadic = flatWeight-normalized

law-unit-support : DyadicLaw → Set
law-unit-support flatDyadic =
  flatUnit-positive × flatUnit-negative-positive

law-zero-support : DyadicLaw → Set
law-zero-support flatDyadic = flatZero-positive

law-universal-support : DyadicLaw → Set
law-universal-support flatDyadic = flatUniversal-positive

flatDyadicNormalized : law-normalized flatDyadic
flatDyadicNormalized = flatWeight-normalized

flatDyadicUnitSupport : law-unit-support flatDyadic
flatDyadicUnitSupport = flatUnit-positive , flatUnit-negative-positive

flatDyadicZeroSupport : law-zero-support flatDyadic
flatDyadicZeroSupport = flatZero-positive

flatDyadicUniversalSupport : law-universal-support flatDyadic
flatDyadicUniversalSupport = flatUniversal-positive
