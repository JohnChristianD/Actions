{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AllSafeCombined_test where

open import Exotic.ERL.FullCoupled.AllSafeCombined using
  ( canonicalMR15PeriodOne
  ; canonicalOpenESPeriodOne
  ; canonicalNoisyNetPeriodOne
  )

mr15-green = canonicalMR15PeriodOne
openes-green = canonicalOpenESPeriodOne
noisynet-green = canonicalNoisyNetPeriodOne
