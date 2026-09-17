{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_<_ ; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

lt-irrefl : ∀ n → n < n → ⊥
lt-irrefl zero ()
lt-irrefl (suc n) (s≤s p) = lt-irrefl n p

plus-zero : ∀ n → n + zero ≡ n
plus-zero zero = refl
plus-zero (suc n) = cong suc (plus-zero n)

plus-suc : ∀ m n → m + suc n ≡ suc (m + n)
plus-suc zero n = refl
plus-suc (suc m) n = cong suc (plus-suc m n)

plus-suc-lt : ∀ m n → m < m + suc n
plus-suc-lt zero n = s≤s z≤n
plus-suc-lt (suc m) n = s≤s (plus-suc-lt m n)

plus-suc-not-self : ∀ m n → m + suc n ≢ m
plus-suc-not-self m n eq = lt-irrefl m
  (subst (λ z → m < z) eq (plus-suc-lt m n))

learnerStep-clock : ∀ {A} K s r →
  L.clock (L.learnerStep K s r) ≡ suc (L.clock s)
learnerStep-clock K s r = refl

learnerNoFixedPoint : ∀ {A} K s r →
  L.learnerStep K s r ≢ s
learnerNoFixedPoint K s r eq =
  plus-suc-not-self (L.clock s) zero
    (trans (sym (learnerStep-clock K s r)) (cong L.clock eq))

iterateLearner-clock : ∀ {A} K n s r →
  L.clock (L.iterateLearner K n s r) ≡ L.clock s + n
iterateLearner-clock K zero s r = sym (plus-zero (L.clock s))
iterateLearner-clock K (suc n) s r =
  trans
    (learnerStep-clock K (L.iterateLearner K n s r) r)
    (cong suc (iterateLearner-clock K n s r))

finiteParameterComplete : ∀ {A : Nat}
  (table : L.QVec A) → (λ a → table a) ≡ table
finiteParameterComplete table = refl

fullCompositionBisimulation : ∀ {A} K s t r →
  s ≡ t → L.learnerStep K s r ≡ L.learnerStep K t r
fullCompositionBisimulation K s t r refl = refl

norm-pair-monotone : ∀ n w x →
  L.l1Weight n ≤ L.l1Weight (L.normStep n w x)
norm-pair-monotone n w x = z≤n

GRUEquivalent : L.GRUState → L.GRUState → Set
GRUEquivalent s t = L.gruPersistent s ≡ L.gruPersistent t

gruPersistentLaw : ∀ s x →
  L.gruPersistent (L.gruStep s x) ≡ L.gruPersistent s
gruPersistentLaw s x = refl

gruStep-respects-equivalence : ∀ s t x →
  GRUEquivalent s t →
  GRUEquivalent (L.gruStep s x) (L.gruStep t x)
gruStep-respects-equivalence s t x e =
  trans (gruPersistentLaw s x)
    (trans e (sym (gruPersistentLaw t x)))

mobiusAssociative : ∀ f g h x →
  L.run (L.composeMobius (L.composeMobius f g) h) x ≡
  L.run (L.composeMobius f (L.composeMobius g h)) x
mobiusAssociative f g h x = refl

prefixAction-law : ∀ T n x →
  L.run (L.prefixAction T (suc n)) x ≡
  L.run (L.atDepth T n) (L.run (L.prefixAction T n) x)
prefixAction-law T n x = refl

traceInput : L.MobiusTrace → Nat → L.Int8 → L.Int8
traceInput T n x = L.run (L.prefixAction T n) x

traceGRU : L.MobiusTrace → Nat → L.GRUState → L.Int8 → L.GRUState
traceGRU T zero s x = s
traceGRU T (suc n) s x =
  L.gruStep (traceGRU T n s x) (traceInput T n x)

traceGRU-step-law : ∀ T n s x →
  traceGRU T (suc n) s x ≡
  L.gruStep (traceGRU T n s x)
    (L.run (L.atDepth T n) (traceInput T n x))
traceGRU-step-law T n s x =
  cong (λ u → L.gruStep (traceGRU T n s x) u)
    (prefixAction-law T n x)

semidirectMobiusStep : L.MobiusAction → L.GRUState → L.Int8 → L.GRUState
semidirectMobiusStep m s x = L.gruStep s (L.run m x)

semidirect-product-law : ∀ f g s x →
  semidirectMobiusStep (L.composeMobius f g) s x ≡
  semidirectMobiusStep f s (L.run g x)
semidirect-product-law f g s x = refl

trace-prefix-semidirect : ∀ T n s x →
  semidirectMobiusStep (L.prefixAction T n) s x ≡
  L.gruStep s (traceInput T n x)
trace-prefix-semidirect T n s x = refl

trace-depth-invariant : ∀ T n s x →
  L.gruPersistent (traceGRU T n s x) ≡ L.gruPersistent s
trace-depth-invariant T zero s x = refl
trace-depth-invariant T (suc n) s x =
  trans
    (L.gruPersistentLaw (traceGRU T n s x) (traceInput T n x))
    (trace-depth-invariant T n s x)

record SparsemaxKKTData (A : Nat) : Set where
  constructor sparsemaxKKTData
  field
    supportSizeK : Nat
    temperatureK : Nat
    thresholdSum : Nat
    supportNonempty : supportSizeK ≢ zero
    denominatorK : Nat
    denominatorLaw : denominatorK ≡ supportSizeK * temperatureK
    supportThresholdPositive : Fin A → Set
    supportThresholdZero : Fin A → Set
    numerator : Fin A → Nat
    numeratorSum : Nat
    simplexLaw : numeratorSum ≡ denominatorK
open SparsemaxKKTData public

sparsemaxKKT-simplex : ∀ {A} (W : SparsemaxKKTData A) →
  numeratorSum W ≡ denominatorK W
sparsemaxKKT-simplex W = simplexLaw W

sparsemaxKKT-denominator : ∀ {A} (W : SparsemaxKKTData A) →
  denominatorK W ≡ supportSizeK W * temperatureK W
denominatorK W = denominatorLaw W

record CNNLocalOperator (X R : Set) : Set where
  constructor cnnLocalOperator
  field
    encode : X → R
    localNext : R → R
open CNNLocalOperator public

record CNNStackClass (X R : Set) : Set where
  constructor cnnStackClass
  field
    first : CNNLocalOperator X R
    next : R → R
    depth : Nat
open CNNStackClass public

cnnEncode : ∀ {X R} → CNNStackClass X R → Nat → X → R
cnnEncode C zero x = encode (first C) x
cnnEncode C (suc n) x = next C (cnnEncode C n x)

record CNNTransitionClass (X R S : Set) : Set where
  constructor cnnTransitionClass
  field
    representation : X → R
    transitionInput : R → S
    nextState : S → S
open CNNTransitionClass public

cnn-transition-preserves : ∀ {X R S : Set}
  (C : CNNTransitionClass X R S) {x y : X} →
  representation C x ≡ representation C y →
  nextState C (transitionInput C (representation C x)) ≡
  nextState C (transitionInput C (representation C y))
cnn-transition-preserves C h =
  cong (nextState C) (cong (transitionInput C) h)

cnn-class-factorization : ∀ {X R S : Set}
  (C : CNNTransitionClass X R S) (x : X) →
  nextState C (transitionInput C (representation C x)) ≡
  nextState C (transitionInput C (representation C x))
cnn-class-factorization C x = refl
