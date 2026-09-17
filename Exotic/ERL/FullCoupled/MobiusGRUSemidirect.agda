{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusGRUSemidirect where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

infixr 5 _::_

data List (A : Set) : Set where
  nil : List A
  _::_ : A → List A → List A

_++_ : ∀ {A : Set} → List A → List A → List A
nil ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f nil = nil
map f (x :: xs) = f x :: map f xs

record Int8 : Set where
  constructor int8
  field code : Nat
open Int8 public

record MobiusAction : Set where
  constructor mobiusAction
  field run : Int8 → Int8
open MobiusAction public

composeMobius : MobiusAction → MobiusAction → MobiusAction
composeMobius f g = mobiusAction (λ x → run f (run g x))

identityMobius : MobiusAction
identityMobius = mobiusAction (λ x → x)

mobiusAssociative : ∀ f g h x →
  run (composeMobius (composeMobius f g) h) x ≡
  run (composeMobius f (composeMobius g h)) x
mobiusAssociative f g h x = refl

record GRUState : Set where
  constructor gruState
  field hiddenState matrixZ matrixR matrixH noiseZ noiseR noiseH optimizerToken l2Token : Int8
open GRUState public

zero8 : Int8
zero8 = int8 0

one8 : Int8
one8 = int8 1

zeroGRU : GRUState
zeroGRU = gruState zero8 one8 one8 one8 zero8 zero8 zero8 zero8 zero8

gruStep : GRUState → Int8 → GRUState
gruStep s x =
  gruState x (matrixZ s) (matrixR s) (matrixH s)
    (noiseZ s) (noiseR s) (noiseH s)
    (optimizerToken s) (l2Token s)

record TraceStep : Set where
  constructor traceStep
  field depth : Nat
        action : MobiusAction
open TraceStep public

Trace : Nat → Set
Trace zero = List TraceStep
Trace (suc n) = List TraceStep

mobiusTransform : MobiusAction → GRUState → Int8 → GRUState
mobiusTransform m s x = gruStep s (run m x)

iterateMobiusGRU : List MobiusAction → GRUState → Int8 → GRUState
iterateMobiusGRU nil s x = s
iterateMobiusGRU (m :: ms) s x = iterateMobiusGRU ms (mobiusTransform m s x) x

iterateMobiusGRU-append : ∀ xs ys s x →
  iterateMobiusGRU (xs ++ ys) s x ≡
  iterateMobiusGRU ys (iterateMobiusGRU xs s x) x
iterateMobiusGRU-append nil ys s x = refl
iterateMobiusGRU-append (m :: xs) ys s x =
  iterateMobiusGRU-append xs ys (mobiusTransform m s x) x

prefixMobius : List MobiusAction → List MobiusAction
prefixMobius nil = nil
prefixMobius (m :: ms) =
  composeMobius m identityMobius :: map (composeMobius m) (prefixMobius ms)

prefixMobius-step : ∀ m ms x →
  run (composeMobius m identityMobius) x ≡ run m x
prefixMobius-step m ms x = refl

scanAction : List MobiusAction → MobiusAction
scanAction nil = identityMobius
scanAction (m :: ms) = composeMobius (scanAction ms) m

scanAction-append : ∀ xs ys →
  scanAction (xs ++ ys) ≡ composeMobius (scanAction ys) (scanAction xs)
scanAction-append nil ys = refl
scanAction-append (m :: xs) ys =
  cong (λ z → composeMobius z m) (scanAction-append xs ys)

semidirectStep : List MobiusAction → GRUState → Int8 → GRUState
semidirectStep ms s x = iterateMobiusGRU ms s x

semidirect-prefix-law : ∀ xs ys s x →
  semidirectStep (xs ++ ys) s x ≡
  semidirectStep ys (semidirectStep xs s x) x
semidirect-prefix-law = iterateMobiusGRU-append

semidirect-scan-law : ∀ ms s x →
  semidirectStep ms s x ≡
  gruStep s (run (scanAction ms) x)
semidirect-scan-law nil s x = refl
semidirect-scan-law (m :: ms) s x =
  trans
    (semidirect-scan-law ms (mobiusTransform m s x) x)
    refl

mobius-depth-invariant : ∀ ms s x →
  matrixZ (semidirectStep ms s x) ≡ matrixZ s
mobius-depth-invariant nil s x = refl
mobius-depth-invariant (m :: ms) s x = mobius-depth-invariant ms (mobiusTransform m s x) x

mobius-optimizer-token-invariant : ∀ ms s x →
  optimizerToken (semidirectStep ms s x) ≡ optimizerToken s
mobius-optimizer-token-invariant nil s x = refl
mobius-optimizer-token-invariant (m :: ms) s x = mobius-optimizer-token-invariant ms (mobiusTransform m s x) x
