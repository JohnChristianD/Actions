{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DeterministicQSA where

open import Agda.Builtin.Equality using (_≡_; refl; sym; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Exotic.efficient_chad.Int8 using (Int8)
open import Exotic.ERL.Exploration.ExplorationTheoremSchema using
  ( Reach
  ; there
  ; here
  ; Irreducible
  ; SelfLoop
  ; PeriodOne
  ; periodOne-from-components
  )
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using
  ( Fixed
  ; LyapunovCertificate
  ; energy
  ; strictDecrease
  ; iterate
  ; iterate-shift
  ; noNontrivialFiniteCycle
  ; OrbitNonFixed
  )
open import Exotic.ERL.FullCoupled.GRUCompositionAlgebra using
  ( GRUState
  ; stepAction
  )

------------------------------------------------------------------------
-- Small constructive sum used for finite decidable state equality.
------------------------------------------------------------------------

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

record HasDecidableEquality (S : Set) : Set₁ where
  constructor decidableEquality
  field
    decide : (x y : S) → (x ≡ y) ⊎ (x ≢ y)

open HasDecidableEquality public

------------------------------------------------------------------------
-- Finite/deterministic QSA-style convergence certificate.
--
-- This is deliberately not a stochastic-approximation theorem. It is the
-- exact finite deterministic contract available from strict Nat-valued
-- descent: every non-fixed step spends one unit of a well-founded rank.
------------------------------------------------------------------------

record EventuallyFixed {S : Set} (step : S → S) (s : S) : Set where
  constructor eventuallyFixed
  field
    steps : Nat
    terminal : Fixed step (iterate step steps s)

open EventuallyFixed public

record ConvergesTo {S : Set} (step : S → S) (target s : S) : Set where
  constructor convergesTo
  field
    stepsToTarget : Nat
    targetEquality : iterate step stepsToTarget s ≡ target

open ConvergesTo public

zeroCannotDescend : ∀ {n : Nat} → n < zero → ⊥
zeroCannotDescend ()

le-refl-nat : ∀ n → n ≤ n
le-refl-nat zero = z≤n
le-refl-nat (suc n) = s≤s (le-refl-nat n)

le-zero-is-zero : ∀ {n : Nat} → n ≤ zero → n ≡ zero
le-zero-is-zero z≤n = refl
le-zero-is-zero (s≤s ())

lt-le-trans :
  ∀ {m n k : Nat} → m < n → n ≤ k → m < k
lt-le-trans {m} {zero} {k} p z≤n = zeroCannotDescend p
lt-le-trans p (s≤s q) = s≤s (lt-le-trans p q)

lt-suc-to-le :
  ∀ {m n : Nat} → m < suc n → m ≤ n
lt-suc-to-le {zero} p = z≤n
lt-suc-to-le {suc m} (s≤s p) = p

eventuallyFixedFromLyapunov :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step)
  (D : HasDecidableEquality S)
  (s : S) →
  EventuallyFixed step s
eventuallyFixedFromLyapunov L D s =
  go (energy L s) s (le-refl-nat (energy L s))
  where
  go :
    ∀ (bound : Nat) (s : S) →
    energy L s ≤ bound →
    EventuallyFixed step s
  go zero s bound with decide D s (step s)
  ... | inj₁ fixed = eventuallyFixed zero fixed
  ... | inj₂ moving =
    let
      eq-zero : energy L s ≡ zero
      eq-zero = le-zero-is-zero bound
      impossible : energy L (step s) < zero
      impossible =
        subst
          (λ z → energy L (step s) < z)
          eq-zero
          (strictDecrease L s moving)
    in zeroCannotDescend impossible
  go (suc bound) s boundProof with decide D s (step s)
  ... | inj₁ fixed = eventuallyFixed zero fixed
  ... | inj₂ moving =
    let
      strict : energy L (step s) < energy L s
      strict = strictDecrease L s moving
      bounded : energy L (step s) < suc bound
      bounded = lt-le-trans strict boundProof
      nextBound : energy L (step s) ≤ bound
      nextBound = lt-suc-to-le bounded
      next : EventuallyFixed step (step s)
      next = go bound (step s) nextBound
      k = steps next
      p = iterate-shift step k s
      terminal' : Fixed step (iterate step (suc k) s)
      terminal' =
        subst
          (λ z → Fixed step z)
          p
          (terminal next)
    in eventuallyFixed (suc k) terminal'

------------------------------------------------------------------------
-- Unique-fixed-point form: this is the clean finite deterministic
-- convergence statement to use when the optimizer has a unique terminal.
------------------------------------------------------------------------

record UniqueFixedPoint
  {S : Set}
  (step : S → S)
  (target : S) : Set where
  constructor uniqueFixedPoint
  field
    targetFixed : Fixed step target
    uniqueFixed : ∀ {s} → Fixed step s → s ≡ target

open UniqueFixedPoint public

record DeterministicQSAStyleCertificate
  (S : Set)
  (step : S → S) : Set₁ where
  constructor deterministicQSAStyleCertificate
  field
    lyapunov : LyapunovCertificate S step
    decidableEquality : HasDecidableEquality S
    target : S
    terminal : UniqueFixedPoint step target

open DeterministicQSAStyleCertificate public

deterministicQSAStyleConvergence :
  ∀ {S : Set} {step : S → S}
  (C : DeterministicQSAStyleCertificate S step)
  (s : S) →
  ConvergesTo step (target C) s
deterministicQSAStyleConvergence C s =
  let
    ev = eventuallyFixedFromLyapunov
      (lyapunov C)
      (decidableEquality C)
      s
    k = steps ev
    fixed-at-k = terminal ev
    reaches-target :
      iterate step k s ≡ target C
    reaches-target = uniqueFixed C fixed-at-k
  in convergesTo k reaches-target

------------------------------------------------------------------------
-- The n-cycle theorem is exactly the deterministic component of the QSA
-- certificate. Once a Lyapunov certificate exists, no nontrivial finite
-- cycle is possible independently of the application architecture.
------------------------------------------------------------------------

deterministicQSAStyleNoNontrivialCycle :
  ∀ {S : Set} {step : S → S}
  (C : DeterministicQSAStyleCertificate S step)
  {s : S} (n : Nat) →
  iterate step (suc n) s ≡ s →
  OrbitNonFixed s →
  ⊥
deterministicQSAStyleNoNontrivialCycle C =
  noNontrivialFiniteCycle (lyapunov C)

------------------------------------------------------------------------
-- Companion stochastic theorem.
-- A pathwise strict Lyapunov law cannot coexist with a supported two-cycle.
-- This is the exact obstruction behind stochastic exploration: noise can
-- preserve irreducibility/period one only by allowing some non-decreasing
-- support edges (unless the carrier collapses to a trivial state).
------------------------------------------------------------------------

record SupportLyapunov (S : Set) (R : S → S → Set) : Set₁ where
  constructor supportLyapunov
  field
    supportEnergy : S → Nat
    strictSupportDecrease :
      ∀ {s t} → R s t → s ≢ t → supportEnergy t < supportEnergy s

open SupportLyapunov public

noStrongSupportLyapunovTwoCycle :
  ∀ {S : Set} {R : S → S → Set}
  (L : SupportLyapunov S R)
  {x y : S} →
  x ≢ y →
  R x y →
  R y x →
  ⊥
noStrongSupportLyapunovTwoCycle L distinct xy yx =
  let
    reverseDistinct : y ≢ x
    reverseDistinct eq = distinct (sym eq)
    downXY : supportEnergy L y < supportEnergy L x
    downXY = strictSupportDecrease L xy distinct
    downYX : supportEnergy L x < supportEnergy L y
    downYX = strictSupportDecrease L yx reverseDistinct
  in <-irrefl (supportEnergy L x) (<-trans downYX downXY)

------------------------------------------------------------------------
-- Minimal finite stochastic/support counterexample.
-- The relation is fully supported, irreducible, and period-one, while the
-- strong support-wide Lyapunov law is impossible.
------------------------------------------------------------------------

data UnitSupport : Set where
  unitSupport : UnitSupport

data Two : Set where
  leftState : Two
  rightState : Two

twoSupport : Two → Two → Set
twoSupport _ _ = UnitSupport

twoSupportWitness : ∀ x y → twoSupport x y
twoSupportWitness x y = unitSupport

twoIrreducible : Irreducible twoSupport
twoIrreducible x y = there (twoSupportWitness x y) here

twoSelfLoop : SelfLoop twoSupport
twoSelfLoop x = twoSupportWitness x x

twoPeriodOne : PeriodOne twoSupport
twoPeriodOne = periodOne-from-components twoIrreducible twoSelfLoop

twoDistinct : leftState ≢ rightState
twoDistinct ()

twoSupportHasTwoCycle :
  twoSupport leftState rightState
  × twoSupport rightState leftState
-- The product witness is intentionally structural and contains no probability
-- or environment assumptions.
twoSupportHasTwoCycle = unitSupport , unitSupport

noTwoStateStrongSupportLyapunov :
  ¬ (SupportLyapunov Two twoSupport)
noTwoStateStrongSupportLyapunov L =
  noStrongSupportLyapunovTwoCycle
    L twoDistinct
    (twoSupportWitness leftState rightState)
    (twoSupportWitness rightState leftState)

------------------------------------------------------------------------
-- GRU-specific scope.
-- The n-cycle theorem is not a theorem of GRU architecture by itself. A GRU
-- step is simply a deterministic action here; it inherits the cycle theorem
-- only after a Lyapunov certificate for that particular action is supplied.
------------------------------------------------------------------------

gruNoNontrivialFiniteCycle :
  ∀ (x : Int8)
  (L : LyapunovCertificate GRUState (stepAction x))
  {s : GRUState} (n : Nat) →
  iterate (stepAction x) (suc n) s ≡ s →
  OrbitNonFixed s →
  ⊥
gruNoNontrivialFiniteCycle x L =
  noNontrivialFiniteCycle L

------------------------------------------------------------------------
-- Explicitly, no environment, reward-distribution, empirical-performance,
-- or asymptotic-statistical premise appears anywhere in these certificates.
------------------------------------------------------------------------
