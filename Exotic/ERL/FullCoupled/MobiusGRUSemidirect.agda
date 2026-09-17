{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MobiusGRUSemidirect where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Agda.Builtin.Nat using (Nat; zero)

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

Trace : Set
Trace = List MobiusAction

mobiusTransform : MobiusAction → GRUState → Int8 → GRUState
mobiusTransform m s x = gruStep s (run m x)

iterateMobiusGRU : Trace → GRUState → Int8 → GRUState
iterateMobiusGRU nil s x = s
iterateMobiusGRU (m :: ms) s x = iterateMobiusGRU ms (mobiusTransform m s x) x

iterateMobiusGRU-append : ∀ xs ys s x →
  iterateMobiusGRU (xs ++ ys) s x ≡
  iterateMobiusGRU ys (iterateMobiusGRU xs s x) x
iterateMobiusGRU-append nil ys s x = refl
iterateMobiusGRU-append (m :: xs) ys s x =
  iterateMobiusGRU-append xs ys (mobiusTransform m s x) x

prefixMobius : Trace → Trace
prefixMobius nil = nil
prefixMobius (m :: ms) =
  composeMobius m identityMobius :: map (composeMobius m) (prefixMobius ms)

prefixMobius-step : ∀ m ms x →
  run (composeMobius m identityMobius) x ≡ run m x
prefixMobius-step m ms x = refl

scanAction : Trace → MobiusAction
scanAction nil = identityMobius
scanAction (m :: ms) = composeMobius (scanAction ms) m

scanAction-append : ∀ xs ys x →
  run (scanAction (xs ++ ys)) x ≡
  run (composeMobius (scanAction ys) (scanAction xs)) x
scanAction-append nil ys x = refl
scanAction-append (m :: xs) ys x =
  trans
    (scanAction-append xs ys (run m x))
    (mobiusAssociative (scanAction ys) (scanAction xs) m x)

trace-semidirect-law : ∀ xs ys s x →
  iterateMobiusGRU (xs ++ ys) s x ≡
  iterateMobiusGRU ys (iterateMobiusGRU xs s x) x
trace-semidirect-law = iterateMobiusGRU-append

trace-depth-preserves-matrix : ∀ ms s x →
  matrixZ (iterateMobiusGRU ms s x) ≡ matrixZ s
trace-depth-preserves-matrix nil s x = refl
trace-depth-preserves-matrix (m :: ms) s x = trace-depth-preserves-matrix ms (mobiusTransform m s x) x

trace-depth-preserves-optimizer : ∀ ms s x →
  optimizerToken (iterateMobiusGRU ms s x) ≡ optimizerToken s
trace-depth-preserves-optimizer nil s x = refl
trace-depth-preserves-optimizer (m :: ms) s x = trace-depth-preserves-optimizer ms (mobiusTransform m s x) x
