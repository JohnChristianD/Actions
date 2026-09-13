{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SoftsignGatedRepresentation where

open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.efficient_chad.SoftsignGatedComposition using
  ( softsignGatedForwardLaw-proof
  ; softsignGatedPullbackLaw-proof
  )

-- Canonical exploration boundary: finite gate signal × learner signal.
-- Coupled Noisy-Net coordinates are related through a separate factor module.
SoftsignGatedRepresentation : Set
SoftsignGatedRepresentation = Int8 × Int8

data SoftsignGatedStep :
    SoftsignGatedRepresentation → SoftsignGatedRepresentation → Set where
  softsignTarget : ∀ {s} → (r : SoftsignGatedRepresentation)
    → SoftsignGatedStep s r

softsignGatedForward-composed = softsignGatedForwardLaw-proof
softsignGatedPullback-composed = softsignGatedPullbackLaw-proof
