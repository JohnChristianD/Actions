{-# OPTIONS --safe #-}

module Exotic.ERL.Extraction.Agda2HSMain where

open import Haskell.Prelude
open import Data.Fin using (toℕ)
open import Exotic.efficient_chad.Int8 using (code; one8; zero8; Int8)
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Parameters
  ; parameters
  ; Token
  ; token
  ; Window2
  ; window2
  ; learnForward
  )

sampleParameters : Parameters
sampleParameters = parameters one8 one8 one8 one8 one8 one8

sampleToken : Token
sampleToken = token one8 zero8 zero8 one8

sampleWindow : Window2
sampleWindow = window2 sampleToken sampleToken

learnerExample : Int8
learnerExample = learnForward sampleParameters sampleWindow

learnerExampleCode : Nat
learnerExampleCode = toℕ (code learnerExample)
