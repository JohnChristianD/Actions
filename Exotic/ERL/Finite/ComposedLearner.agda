{-# OPTIONS --safe #-}

module Exotic.ERL.Finite.ComposedLearner where

open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.Finite.Int8Vector using (Int8Vector4; vec4; x0; x1; x2; x3)
open import Exotic.ERL.Finite.Activation using (softsignQ8; signReLUQ8; cReLU8)
open import Exotic.ERL.Finite.Haar using (haar4)
open import Exotic.ERL.Finite.TrueOnlineTD using
  ( TrueOnlineState
  ; learnerStep
  )

map4 : (Int8 → Int8) → Int8Vector4 → Int8Vector4
map4 f v = vec4
  (f (x0 v))
  (f (x1 v))
  (f (x2 v))
  (f (x3 v))

haarSignReLU4 : Int8Vector4 → Int8Vector4
haarSignReLU4 v = map4 signReLUQ8 (haar4 v)

haarCReLU4 : Int8Vector4 → Int8Vector4
haarCReLU4 v = map4 cReLU8 (haar4 v)

haarSignReLUSoftsign4 : Int8Vector4 → Int8Vector4
haarSignReLUSoftsign4 v = map4 softsignQ8 (haarSignReLU4 v)

composedSoftsignStep :
  Int8 → Int8Vector4 → Int8Vector4 → TrueOnlineState → TrueOnlineState
composedSoftsignStep reward phi nextPhi state =
  learnerStep
    reward
    (haarSignReLUSoftsign4 phi)
    (haarSignReLUSoftsign4 nextPhi)
    state

composedCReLUStep :
  Int8 → Int8Vector4 → Int8Vector4 → TrueOnlineState → TrueOnlineState
composedCReLUStep reward phi nextPhi state =
  learnerStep
    reward
    (haarCReLU4 phi)
    (haarCReLU4 nextPhi)
    state
