{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteVJP where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; int8Add
  ; int8Mul
  ; int8OfNat
  ; zero8
  ; one8
  )

------------------------------------------------------------------------
-- Finite primal/pullback semantics.
--
-- The pullback is an explicit finite cotangent transport.  The record is
-- intentionally small: the canonical learner only needs compositional scalar
-- primitives, while the finite Int8 ring supplies the carrier and algebra.
------------------------------------------------------------------------

record VJP : Set where
  constructor vjp
  field
    primal : Int8
    pullback : Int8 → Int8

open VJP public

idVJP : Int8 → VJP
idVJP x = vjp x (λ c → c)

addVJP : Int8 → Int8 → VJP
addVJP x y = vjp (int8Add x y) (λ c → c)

mulVJP-left : Int8 → Int8 → VJP
mulVJP-left x y = vjp (int8Mul x y) (λ c → int8Mul c y)

mulVJP-right : Int8 → Int8 → VJP
mulVJP-right x y = vjp (int8Mul x y) (λ c → int8Mul c x)

compose : (Int8 → VJP) → (Int8 → VJP) → Int8 → VJP
compose f g x with g x
... | vjp gx pg with f gx
...   | vjp y pf =
      vjp y (λ c → pg (pf c))

composePrimal : ∀ (f g : Int8 → VJP) (x : Int8) →
  primal (compose f g x) ≡ primal (f (primal (g x)))
composePrimal f g x = refl

composePullback : ∀ (f g : Int8 → VJP) (x c : Int8) →
  pullback (compose f g x) c ≡
  pullback (g x) (pullback (f (primal (g x))) c)
composePullback f g x c = refl

addVJPLaw : ∀ (x y c : Int8) →
  pullback (addVJP x y) c ≡ c
addVJPLaw x y c = refl

mulVJPLaw : ∀ (x y c : Int8) →
  pullback (mulVJP-left x y) c ≡ int8Mul c y
mulVJPLaw x y c = refl

mulVJPRaw : ∀ (x y c : Int8) →
  pullback (mulVJP-right x y) c ≡ int8Mul c x
mulVJPRaw x y c = refl

zeroPullback : ∀ c → pullback (idVJP zero8) c ≡ c
zeroPullback c = refl

unitPrimal : ∀ x → primal (mulVJP-left x one8) ≡ x
unitPrimal x = refl

------------------------------------------------------------------------
-- A typed two-parameter pullback for one multiplication node.  This is the
-- primitive used by the learner's synchronous parameter commit.
------------------------------------------------------------------------

record ParamVJP : Set where
  constructor paramVjp
  field
    output : Int8
    backward : Int8 → Int8 × Int8

open ParamVJP public

mulParamVJP : Int8 → Int8 → ParamVJP
mulParamVJP x w =
  paramVjp
    (int8Mul x w)
    (λ c → int8Mul c x , int8Mul c w)

mulParamOutput : ∀ (x w : Int8) →
  output (mulParamVJP x w) ≡ int8Mul x w
mulParamOutput x w = refl

mulParamBackward : ∀ (x w c : Int8) →
  backward (mulParamVJP x w) c ≡ (int8Mul c x , int8Mul c w)
mulParamBackward x w c = refl

------------------------------------------------------------------------
-- Snapshot/commit law: the backward pass consumes an immutable snapshot and
-- returns the unique finite update pair used by the caller.
------------------------------------------------------------------------

snapshotCommit : (x w c : Int8) → Int8 × Int8
snapshotCommit x w c =
  let (gx , gw) = backward (mulParamVJP x w) c
  in gx , gw

snapshotCommitLaw : ∀ (x w c : Int8) →
  snapshotCommit x w c ≡ (int8Mul c x , int8Mul c w)
snapshotCommitLaw x w c = refl
