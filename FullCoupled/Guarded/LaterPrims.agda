{-# OPTIONS --cubical --guarded #-}

module FullCoupled.Guarded.LaterPrims where

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

module Prims where
  primitive primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private variable
  ℓ : Level
  A B : Set ℓ

postulate
  Tick : LockU

▹_ : ∀ {ℓ} → Set ℓ → Set ℓ
▹ A = (@tick x : Tick) → A

▸_ : ∀ {ℓ} → ▹ Set ℓ → Set ℓ
▸ A = (@tick x : Tick) → A x

next : ∀ {ℓ} {A : Set ℓ} → A → ▹ A
next a @tick = a

_⊛_ :
  ∀ {ℓ₁ ℓ₂}
  {A : Set ℓ₁}
  {B : Set ℓ₂} →
  ▹ (A → B) → ▹ A → ▹ B
(f ⊛ x) @tick = f @tick (x @tick)

map▹ :
  ∀ {ℓ₁ ℓ₂}
  {A : Set ℓ₁}
  {B : Set ℓ₂} →
  (A → B) → ▹ A → ▹ B
map▹ f x = next f ⊛ x

transpLater-prim :
  ∀ {ℓ₁ ℓ₂}
  {A B : Set ℓ₁} →
  A ≡ B → ▹ A → ▹ B
transpLater-prim refl x = x

transpLater :
  ∀ {ℓ₁ ℓ₂}
  {A B : Set ℓ₁} →
  A ≡ B → ▹ A → ▹ B
transpLater = transpLater-prim

transpLater-test :
  ∀ {A : Set ℓ} (x : ▹ A) →
  transpLater refl x ≡ x
transpLater-test x = refl

hcompLater-prim :
  ∀ {ℓ}
  {A : Set ℓ} →
  ▹ A → ▹ A → ▹ A
hcompLater-prim x y @tick = x @tick

hcompLater :
  ∀ {ℓ}
  {A : Set ℓ} →
  ▹ A → ▹ A → ▹ A
hcompLater = hcompLater-prim

hcompLater-test :
  ∀ {A : Set ℓ} (x y : ▹ A) →
  hcompLater x y ≡ x
hcompLater-test x y = refl

ap :
  ∀ {ℓ₁ ℓ₂}
  {A : Set ℓ₁}
  {B : Set ℓ₂}
  (f : A → B) {x y : A} →
  x ≡ y → f x ≡ f y
ap f refl = refl

_$>_ :
  ∀ {ℓ₁ ℓ₂}
  {A : Set ℓ₁}
  {B : Set ℓ₂} →
  ▹ A → (A → B) → ▹ B
x $> f = map▹ f x

postulate
  later-ext :
    ∀ {ℓ} {A : Set ℓ} {x y : ▹ A} →
    ((@tick t : Tick) → x @t ≡ y @t) →
    x ≡ y

postulate
  dfix :
    ∀ {ℓ} {A : Set ℓ} →
    (▹ A → A) → A

  pfix :
    ∀ {ℓ} {A : Set ℓ} →
    (▹ A → A) → ▹ A

  pfix' :
    ∀ {ℓ} {A : Set ℓ} →
    (▹ A → A) → A

fix : ∀ {ℓ} {A : Set ℓ} → (▹ A → A) → A
fix = dfix

data Stream (A : Set) : Set where
  stream : (A → ▹ (Stream A)) → Stream A

gStream : ∀ {A : Set} → (A → ▹ (Stream A)) → Stream A
gStream = stream

repeat : ∀ {A : Set} → A → Stream A
repeat a = gStream (λ _ → next (repeat a))

repeat-eq : ∀ {A : Set} (a : A) → repeat a ≡ repeat a
repeat-eq a = refl

map : ∀ {A B : Set} → (A → B) → Stream A → Stream B
map f (stream k) = stream (λ a → map▹ (map f) (k a))

map-eq : ∀ {A B : Set} (f : A → B) (s : Stream A) → map f s ≡ map f s
map-eq f s = refl

map-repeat :
  ∀ {A B : Set} (f : A → B) (a : A) →
  map f (repeat a) ≡ repeat (f a)
map-repeat f a = refl
