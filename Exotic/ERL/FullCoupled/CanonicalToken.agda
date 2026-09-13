{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalToken where

open import Exotic.efficient_chad.Int8 using (Int8)

record Token : Set where
  constructor token
  field
    observation previousAction reward nextObservation : Int8

open Token public
