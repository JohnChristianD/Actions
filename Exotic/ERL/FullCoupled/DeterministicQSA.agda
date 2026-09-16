{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DeterministicQSA where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

sym : ∀ {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

subst : ∀ {A : Set} {x y : A} (P : A -> Set) -> x ≡ y -> P x -> P y
subst P refl p = p

data ⊥ : Set where

⊥-elim : ∀ {A : Set} -> ⊥ -> A
⊥-elim ()

¬_ : Set -> Set
¬ A = A -> ⊥

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A -> A ⊎ B
  inj₂ : B -> A ⊎ B

infix 4 _≤_ _<_
data _≤_ : Nat -> Nat -> Set where
  z≤n : ∀ {n} -> zero ≤ n
  s≤s : ∀ {m n} -> m ≤ n -> suc m ≤ suc n

_<_ : Nat -> Nat -> Set
m < n = suc m ≤ n

le-refl-nat : ∀ n -> n ≤ n
le-refl-nat zero = z≤n
le-refl-nat (suc n) = s≤s (le-refl-nat n)

le-trans-nat : ∀ {m n k} -> m ≤ n -> n ≤ k -> m ≤ k
le-trans-nat z≤n q = q
le-trans-nat (s≤s p) (s≤s q) = s≤s (le-trans-nat p q)

le-zero-is-zero : ∀ {n} -> n ≤ zero -> n ≡ zero
le-zero-is-zero z≤n = refl
le-zero-is-zero (s≤s ())

zeroCannotDescend : ∀ {n} -> n < zero -> ⊥
zeroCannotDescend ()

lt-le-trans : ∀ {m n k} -> m < n -> n ≤ k -> m < k
lt-le-trans (s≤s p) (s≤s q) = s≤s (le-trans-nat p q)
lt-le-trans {n = zero} p z≤n = zeroCannotDescend p

lt-suc-to-le : ∀ {m n} -> m < suc n -> m ≤ n
lt-suc-to-le (s≤s p) = p

lt-trans : ∀ {m n k} -> m < n -> n < k -> m < k
lt-trans (s≤s p) (s≤s q) = s≤s (le-trans-nat p q)

lt-irrefl : ∀ n -> ¬ (n < n)
lt-irrefl zero p = zeroCannotDescend p
lt-irrefl (suc n) (s≤s p) = lt-irrefl n p

record HasDecidableEquality (S : Set) : Set₁ where
  constructor decidableEquality
  field
    decide : (x y : S) -> (x ≡ y) ⊎ (x ≢ y)

open HasDecidableEquality public

Fixed : ∀ {S : Set} -> (S -> S) -> S -> Set
Fixed step s = step s ≡ s

OrbitNonFixed : ∀ {S : Set} -> (S -> S) -> S -> Set
OrbitNonFixed step s = s ≢ step s

iterate : ∀ {S : Set} -> (S -> S) -> Nat -> S -> S
iterate step zero s = s
iterate step (suc n) s = step (iterate step n s)

iterate-shift : ∀ {S : Set} (step : S -> S) (n : Nat) (s : S) ->
  iterate step n (step s) ≡ iterate step (suc n) s
iterate-shift step zero s = refl
iterate-shift step (suc n) s = cong step (iterate-shift step n s)

record LyapunovCertificate (S : Set) (step : S -> S) : Set₁ where
  constructor lyapunovCertificate
  field
    energy : S -> Nat
    strictDecrease : ∀ {s} -> s ≢ step s -> energy (step s) < energy s

open LyapunovCertificate public

record EventuallyFixed {S : Set} (step : S -> S) (s : S) : Set where
  constructor eventuallyFixed
  field
    steps : Nat
    terminal : Fixed step (iterate step steps s)

open EventuallyFixed public

record ConvergesTo {S : Set} (step : S -> S) (target s : S) : Set where
  constructor convergesTo
  field
    stepsToTarget : Nat
    targetEquality : iterate step stepsToTarget s ≡ target

open ConvergesTo public

eventuallyFixedFromLyapunov :
  ∀ {S : Set} {step : S -> S}
  (L : LyapunovCertificate S step)
  (D : HasDecidableEquality S)
  (s : S) -> EventuallyFixed step s
eventuallyFixedFromLyapunov L D s = go (energy L s) s (le-refl-nat (energy L s))
  where
  go : ∀ (bound : Nat) (s : S) -> energy L s ≤ bound -> EventuallyFixed step s
  go zero s bound with decide D s (step s)
  ... | inj₁ fixed = eventuallyFixed zero fixed
  ... | inj₂ moving = zeroCannotDescend
    (subst (λ z -> energy L (step s) < z)
      (le-zero-is-zero bound)
      (strictDecrease L moving))
  go (suc bound) s boundProof with decide D s (step s)
  ... | inj₁ fixed = eventuallyFixed zero fixed
  ... | inj₂ moving =
    let
      strict = strictDecrease L moving
      nextBound = lt-suc-to-le (lt-le-trans strict boundProof)
      next = go bound (step s) nextBound
      k = steps next
      shifted = iterate-shift step k s
      terminal' : Fixed step (iterate step (suc k) s)
      terminal' = subst (λ z -> Fixed step z) shifted (terminal next)
    in eventuallyFixed (suc k) terminal'

record UniqueFixedPoint {S : Set} (step : S -> S) (target : S) : Set where
  constructor uniqueFixedPoint
  field
    targetFixed : Fixed step target
    uniqueFixed : ∀ {s} -> Fixed step s -> s ≡ target

open UniqueFixedPoint public

record DeterministicQSAStyleCertificate (S : Set) (step : S -> S) : Set₁ where
  constructor deterministicQSAStyleCertificate
  field
    lyapunov : LyapunovCertificate S step
    decidableEquality : HasDecidableEquality S
    target : S
    terminal : UniqueFixedPoint step target

open DeterministicQSAStyleCertificate public

deterministicQSAStyleConvergence :
  ∀ {S : Set} {step : S -> S}
  (C : DeterministicQSAStyleCertificate S step) (s : S) ->
  ConvergesTo step (target C) s
deterministicQSAStyleConvergence C s =
  let
    ev = eventuallyFixedFromLyapunov (lyapunov C) (decidableEquality C) s
    k = steps ev
  in convergesTo k (uniqueFixed (terminal C) (terminal ev))

deterministicQSAStyleTargetFixed :
  ∀ {S : Set} {step : S -> S}
  (C : DeterministicQSAStyleCertificate S step) ->
  Fixed step (target C)
deterministicQSAStyleTargetFixed C = targetFixed (terminal C)

deterministicQSAStyleFixedStatesCollapse :
  ∀ {S : Set} {step : S -> S}
  (C : DeterministicQSAStyleCertificate S step)
  {s : S} -> Fixed step s -> s ≡ target C
deterministicQSAStyleFixedStatesCollapse C = uniqueFixed (terminal C)

record SupportLyapunov (S : Set) (R : S -> S -> Set) : Set₁ where
  constructor supportLyapunov
  field
    supportEnergy : S -> Nat
    strictSupportDecrease :
      ∀ {s t} -> R s t -> s ≢ t -> supportEnergy t < supportEnergy s

open SupportLyapunov public

noStrongSupportLyapunovTwoCycle :
  ∀ {S : Set} {R : S -> S -> Set}
  (L : SupportLyapunov S R) {x y : S} ->
  x ≢ y -> R x y -> R y x -> ⊥
noStrongSupportLyapunovTwoCycle L distinct xy yx =
  lt-irrefl (supportEnergy L x)
    (lt-trans
      (strictSupportDecrease L yx (λ eq -> distinct (sym eq)))
      (strictSupportDecrease L xy distinct))

record ClosedSupportOrbit (S : Set) (R : S -> S -> Set) (n : Nat) : Set₁ where
  constructor closedSupportOrbit
  field
    point : Nat -> S
    edge : ∀ i -> i ≤ n -> R (point i) (point (suc i))
    distinct : ∀ i -> i ≤ n -> point i ≢ point (suc i)
    close : point (suc n) ≡ point zero

open ClosedSupportOrbit public

closedSupportOrbitImpossible :
  ∀ {S : Set} {R : S -> S -> Set}
  (L : SupportLyapunov S R) {n : Nat} ->
  ClosedSupportOrbit S R n -> ⊥
closedSupportOrbitImpossible L C =
  let
    descending : ∀ {i} -> i ≤ n ->
      supportEnergy L (point C (suc i)) < supportEnergy L (point C zero)
    descending {zero} p = strictSupportDecrease L (edge C zero p) (distinct C zero p)
    descending {suc i} (s≤s p) =
      lt-trans
        (strictSupportDecrease L (edge C i p) (distinct C i p))
        (descending p)
    impossible = subst
      (λ z -> supportEnergy L z < supportEnergy L (point C zero))
      (close C)
      (descending (le-refl-nat n))
  in lt-irrefl (supportEnergy L (point C zero)) impossible

supportRelationAntisymmetricOffDiagonal :
  ∀ {S : Set} {R : S -> S -> Set}
  (L : SupportLyapunov S R) {x y : S} ->
  x ≢ y -> R x y -> ¬ R y x
supportRelationAntisymmetricOffDiagonal L distinct xy yx =
  noStrongSupportLyapunovTwoCycle L distinct xy yx

data ReachPath {S : Set} (R : S -> S -> Set) : S -> S -> Set where
  here : ∀ {s} -> ReachPath R s s
  there : ∀ {s t u} -> R s t -> ReachPath R t u -> ReachPath R s u

Irreducible : ∀ {S : Set} -> (S -> S -> Set) -> Set
Irreducible R = ∀ s t -> ReachPath R s t

SelfLoop : ∀ {S : Set} -> (S -> S -> Set) -> Set
SelfLoop R = ∀ s -> R s s

record PeriodOne {S : Set} (R : S -> S -> Set) : Set where
  constructor periodOne
  field
    irreducible : Irreducible R
    selfLoop : SelfLoop R

periodOne-from-components :
  ∀ {S : Set} {R : S -> S -> Set} ->
  Irreducible R -> SelfLoop R -> PeriodOne R
periodOne-from-components r l = periodOne r l

data UnitSupport : Set where
  unitSupport : UnitSupport

data Two : Set where
  leftState : Two
  rightState : Two

twoSupport : Two -> Two -> Set
twoSupport _ _ = UnitSupport

twoSupportWitness : ∀ x y -> twoSupport x y
twoSupportWitness _ _ = unitSupport

twoIrreducible : Irreducible twoSupport
twoIrreducible x y = there (twoSupportWitness x y) here

twoSelfLoop : SelfLoop twoSupport
twoSelfLoop x = twoSupportWitness x x

twoPeriodOne : PeriodOne twoSupport
twoPeriodOne = periodOne-from-components twoIrreducible twoSelfLoop

twoDistinct : leftState ≢ rightState
twoDistinct ()

twoSupportLeftToRight : twoSupport leftState rightState
twoSupportLeftToRight = twoSupportWitness leftState rightState

twoSupportRightToLeft : twoSupport rightState leftState
twoSupportRightToLeft = twoSupportWitness rightState leftState

noTwoStateStrongSupportLyapunov : ¬ (SupportLyapunov Two twoSupport)
noTwoStateStrongSupportLyapunov L =
  noStrongSupportLyapunovTwoCycle L twoDistinct
    twoSupportLeftToRight twoSupportRightToLeft
