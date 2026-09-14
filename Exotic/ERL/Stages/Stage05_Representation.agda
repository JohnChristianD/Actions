{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage05_Representation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Exotic.ERL.GRU.Int8GRU using
  ( Vec2
  ; DyadicGRU
  ; haar2016
  ; dyadicRoPE
  ; representationPreprocess
  )

record Representation : Set₁ where
  constructor representation
  field
    gru : DyadicGRU

open Representation public

applyRepresentation : Representation → Vec2 → Vec2
applyRepresentation r x =
  representationPreprocess haar2016 dyadicRoPE x

representationBoundary : ∀ (r : Representation) x →
  applyRepresentation r x ≡
  representationPreprocess haar2016 dyadicRoPE x
representationBoundary r x = refl
