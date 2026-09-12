{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.FullCoupledStep where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8Mul
  ; int8OfNat
  ; code
  ; zero8
  ; one8
  )
open import Data.Fin using (toℕ)
open import Data.Nat using (_∸_)
open import Exotic.ERL.Finite.Int8Vector using
  ( Int8Vector4
  ; vec4
  ; x0
  )
open import Exotic.ERL.Finite.TrueOnlineTD using
  ( TrueOnlineState
  ; initialState
  ; learnerStep
  ; theta
  ; trace
  ; previousFeature
  ; previousValue
  )
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Parameters
  ; parameters
  ; Window2
  ; Token
  ; previous
  ; observation
  ; previousAction
  ; reward
  ; nextObservation
  )

representationScalar : Window2 → Int8
representationScalar w =
  int8Add
    (int8Add (observation (previous w)) (previousAction (previous w)))
    (int8Add (reward (previous w)) (nextObservation (previous w)))

representationFeature : Window2 → Int8Vector4
representationFeature w =
  let h = representationScalar w
  in vec4 h zero8 zero8 zero8

afterTrueOnline : Window2 → TrueOnlineState → TrueOnlineState
afterTrueOnline w s =
  let phi = representationFeature w
  in learnerStep (reward (previous w)) phi phi s

record FullCoupledState : Set where
  constructor fullCoupledState
  field
    params : Parameters
    criticState : TrueOnlineState

open FullCoupledState public

fullCoupledInitial : Parameters → FullCoupledState
fullCoupledInitial p = fullCoupledState p initialState

fullCoupledStep : Window2 → FullCoupledState → FullCoupledState
fullCoupledStep w s =
  fullCoupledState (params s) (afterTrueOnline w (criticState s))

fullCoupledZero : ∀ p → fullCoupledStep
  (let t = previous (recordWindow p) in recordWindow p)
  (fullCoupledInitial p) ≡ fullCoupledInitial p
fullCoupledZero p = refl
  where
  recordWindow : Parameters → Window2
  recordWindow p =
    let t =
      recordToken
        (w1 p) (w2 p) (w3 p) (w4 p)
    in recordWindow2 t t

  recordToken : Int8 → Int8 → Int8 → Int8 → Token
  recordToken a b c d =
    let _ = int8Add a (int8Mul b c)
    in recordToken0 a b c d

  recordToken0 : Int8 → Int8 → Int8 → Int8 → Token
  recordToken0 a b c d =
    recordTokenConstructor a b c d

  recordTokenConstructor : Int8 → Int8 → Int8 → Int8 → Token
  recordTokenConstructor a b c d =
    Token.token a b c d

  recordWindow2 : Token → Token → Window2
  recordWindow2 a b =
    Window2.window2 a b
