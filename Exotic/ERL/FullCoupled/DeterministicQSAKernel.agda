{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.DeterministicQSAKernel where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl p = p

infix 4 _≤_ _<_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

lt-irrefl : ∀ n → ¬ (n < n)
lt-irrefl zero ()
lt-irrefl (suc n) (s≤s p) = lt-irrefl n p

_⊎_ : Set → Set → Set
A ⊎ B = Choice A B

data Choice (A B : Set) : Set where
  inj₁ : A → Choice A B
  inj₂ : B → Choice A B

¬_ : Set → Set
¬ A = A → ⊥

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

record HasDecidableEquality (S : Set) : Set₁ where
  constructor decidableEquality
  field
    decide : (x y : S) → (x ≡ y) ⊎ (x ≢ y)
open HasDecidableEquality public

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate step zero s = s
iterate step (suc n) s = step (iterate step n s)

iterate-shift : ∀ {S : Set} (step : S → S) (n : Nat) (s : S) →
  iterate step n (step s) ≡ iterate step (suc n) s
iterate-shift step zero s = refl
iterate-shift step (suc n) s = cong-step (iterate-shift step n s)
  where
    cong-step : ∀ {A B : Set} {f : A → B} {x y : A} →
      x ≡ y → f x ≡ f y
    cong-step refl = refl

record LyapunovCertificate (S : Set) (step : S → S) : Set₁ where
  constructor lyapunovCertificate
  field
    energy : S → Nat
    strictDecrease : ∀ {s} → s ≢ step s → energy (step s) < energy s
open LyapunovCertificate public

record EventuallyFixed {S : Set} (step : S → S) (s : S) : Set where
  constructor eventuallyFixed
  field
    steps : Nat
    terminal : step (iterate step steps s) ≡ iterate step steps s
open EventuallyFixed public

le-refl : ∀ n → n ≤ n
le-refl zero = z≤n
le-refl (suc n) = s≤s (le-refl n)

le-zero-is-zero : ∀ {n} → n ≤ zero → n ≡ zero
le-zero-is-zero z≤n = refl
le-zero-is-zero (s≤s ())

zeroCannotDescend : ∀ {n} → n < zero → ⊥
zeroCannotDescend ()

lt-le-trans : ∀ {m n k} → m < n → n ≤ k → m < k
lt-le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)
lt-le-trans {n = zero} p z≤n = zeroCannotDescend p
  where
    le-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    le-trans z≤n q = q
    le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)

lt-suc-to-le : ∀ {m n} → m < suc n → m ≤ n
lt-suc-to-le (s≤s p) = p

eventuallyFixedFromLyapunov :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step)
  (D : HasDecidableEquality S)
  (s : S) → EventuallyFixed step s
eventuallyFixedFromLyapunov L D s = go (energy L s) s (le-refl (energy L s))
  where
    go : ∀ (bound : Nat) (s : S) → energy L s ≤ bound → EventuallyFixed step s
    go zero s p with decide D s (step s)
    ... | inj₁ fixed = eventuallyFixed zero fixed
    ... | inj₂ moving = zeroCannotDescend
      (subst (λ z → energy L (step s) < z)
        (le-zero-is-zero p)
        (strictDecrease L moving))
    go (suc bound) s p with decide D s (step s)
    ... | inj₁ fixed = eventuallyFixed zero fixed
    ... | inj₂ moving =
      let
        strict = strictDecrease L moving
        nextBound = lt-suc-to-le (lt-le-trans strict p)
        next = go bound (step s) nextBound
        k = steps next
      in eventuallyFixed
        (suc k)
        (subst
          (λ z → step z ≡ z)
          (sym (iterate-shift step k s))
          (terminal next))

record UniqueFixedPoint {S : Set} (step : S → S) (target : S) : Set where
  constructor uniqueFixedPoint
  field
    targetFixed : step target ≡ target
    uniqueFixed : ∀ {s} → step s ≡ s → s ≡ target
open UniqueFixedPoint public

record DeterministicQSAStyleCertificate (S : Set) (step : S → S) : Set₁ where
  constructor deterministicQSAStyleCertificate
  field
    lyapunov : LyapunovCertificate S step
    decidableEquality : HasDecidableEquality S
    target : S
    terminal : UniqueFixedPoint step target
open DeterministicQSAStyleCertificate public

deterministicQSAStyleConvergence :
  ∀ {S : Set} {step : S → S}
  (C : DeterministicQSAStyleCertificate S step) (s : S) →
  iterate step (steps (eventuallyFixedFromLyapunov (lyapunov C) (decidableEquality C) s)) s
  ≡ target C
deterministicQSAStyleConvergence C s =
  uniqueFixed (terminal C) (terminal (eventuallyFixedFromLyapunov (lyapunov C) (decidableEquality C) s))

record SupportLyapunov (S : Set) (R : S → S → Set) : Set₁ where
  constructor supportLyapunov
  field
    supportEnergy : S → Nat
    strictSupportDecrease : ∀ {s t} → R s t → s ≢ t → supportEnergy t < supportEnergy s
open SupportLyapunov public

noStrongSupportLyapunovTwoCycle :
  ∀ {S : Set} {R : S → S → Set}
  (L : SupportLyapunov S R) {x y : S} →
  x ≢ y → R x y → R y x → ⊥
noStrongSupportLyapunovTwoCycle L distinct xy yx =
  lt-irrefl (supportEnergy L x) (<-trans downYX downXY)
  where
    downXY : supportEnergy L y < supportEnergy L x
    downXY = strictSupportDecrease L xy distinct
    reverseDistinct : y ≢ x
    reverseDistinct eq = distinct (sym eq)
    downYX : supportEnergy L x < supportEnergy L y
    downYX = strictSupportDecrease L yx reverseDistinct
    <-trans : ∀ {a b c} → a < b → b < c → a < c
    <-trans (s≤s p) (s≤s q) =
      s≤s (le-trans p q)
      where
        le-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
        le-trans z≤n q = q
        le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)

record ClosedSupportOrbit (S : Set) (R : S → S → Set) (n : Nat) : Set₁ where
  constructor closedSupportOrbit
  field
    point : Nat → S
    edge : ∀ i → i ≤ n → R (point i) (point (suc i))
    distinct : ∀ i → i ≤ n → point i ≢ point (suc i)
    close : point (suc n) ≡ point zero
open ClosedSupportOrbit public

closedSupportOrbitImpossible :
  ∀ {S : Set} {R : S → S → Set}
  (L : SupportLyapunov S R) {n : Nat} →
  ClosedSupportOrbit S R n → ⊥
closedSupportOrbitImpossible L C =
  lt-irrefl (supportEnergy L (point C zero)) impossible
  where
    le-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    le-trans z≤n q = q
    le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)
    descend : ∀ {i} → i ≤ n → supportEnergy L (point C (suc i)) < supportEnergy L (point C zero)
    descend {zero} p = strictSupportDecrease L (edge C zero p) (distinct C zero p)
    descend {suc i} (s≤s p) =
      let h = strictSupportDecrease L (edge C i p) (distinct C i p)
          r = descend p
      in lt-trans h r
    lt-trans : ∀ {a b c} → a < b → b < c → a < c
    lt-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)
    impossible = subst
      (λ z → supportEnergy L z < supportEnergy L (point C zero))
      (close C)
      (descend (le-refl n))

record PeriodOne {S : Set} (R : S → S → Set) : Set where
  constructor periodOne
  field
    irreducible : Set
    selfLoop : Set
