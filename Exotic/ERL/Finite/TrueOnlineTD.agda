{-# OPTIONS --safe #-}

module Exotic.ERL.Finite.TrueOnlineTD where

open import Data.Fin using (toℕ)
open import Data.Nat using (_+_; _∸_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8Add
  ; int8Mul
  ; int8OfNat
  ; zero8
  ; one8
  )
open import Exotic.ERL.Finite.Int8Vector using
  ( Int8Vector4
  ; vec4
  ; x0
  ; x1
  ; x2
  ; x3
  )

typeSub : Int8 → Int8 → Int8
typeSub x y = int8OfNat (256 + toℕ (code x) ∸ toℕ (code y))

scale4 : Int8 → Int8Vector4 → Int8Vector4
scale4 a v = vec4
  (int8Mul a (x0 v))
  (int8Mul a (x1 v))
  (int8Mul a (x2 v))
  (int8Mul a (x3 v))

add4 : Int8Vector4 → Int8Vector4 → Int8Vector4
add4 a b = vec4
  (int8Add (x0 a) (x0 b))
  (int8Add (x1 a) (x1 b))
  (int8Add (x2 a) (x2 b))
  (int8Add (x3 a) (x3 b))

sub4 : Int8Vector4 → Int8Vector4 → Int8Vector4
sub4 a b = vec4
  (typeSub (x0 a) (x0 b))
  (typeSub (x1 a) (x1 b))
  (typeSub (x2 a) (x2 b))
  (typeSub (x3 a) (x3 b))

dot4 : Int8Vector4 → Int8Vector4 → Int8
dot4 a b = int8Add
  (int8Add (int8Mul (x0 a) (x0 b)) (int8Mul (x1 a) (x1 b)))
  (int8Add (int8Mul (x2 a) (x2 b)) (int8Mul (x3 a) (x3 b)))

record TrueOnlineState : Set where
  constructor trueOnlineState
  field
    theta : Int8Vector4
    trace : Int8Vector4
    previousFeature : Int8Vector4
    previousValue : Int8

open TrueOnlineState public

initialState : TrueOnlineState
initialState = trueOnlineState
  (vec4 zero8 zero8 zero8 zero8)
  (vec4 zero8 zero8 zero8 zero8)
  (vec4 zero8 zero8 zero8 zero8)
  zero8

criticValue : Int8Vector4 → Int8Vector4 → Int8
criticValue features parameters = dot4 features parameters

traceStep : Int8Vector4 → TrueOnlineState → Int8Vector4
traceStep phi s =
  add4
    (trace s)
    (scale4
      (typeSub one8 (dot4 phi (trace s)))
      phi)

tdError : Int8 → Int8Vector4 → Int8Vector4 → TrueOnlineState → Int8
tdError reward nextPhi phi s =
  typeSub
    (int8Add reward (criticValue nextPhi (theta s)))
    (criticValue phi (theta s))

learnerStep : Int8 → Int8Vector4 → Int8Vector4 → TrueOnlineState → TrueOnlineState
learnerStep reward phi nextPhi s =
  trueOnlineState newTheta newTrace phi (criticValue phi newTheta)
  where
  delta = tdError reward nextPhi phi s
  newTrace = traceStep phi s
  base = scale4 delta newTrace
  correctionScale = typeSub
    (criticValue phi (theta s))
    (previousValue s)
  correction = scale4 correctionScale (sub4 newTrace phi)
  newTheta = add4 (theta s) (add4 base correction)

exampleFeature : Int8Vector4
exampleFeature = vec4 one8 zero8 zero8 zero8

exampleNextFeature : Int8Vector4
exampleNextFeature = exampleFeature

exampleStep : TrueOnlineState
exampleStep = learnerStep one8 exampleFeature exampleNextFeature initialState
