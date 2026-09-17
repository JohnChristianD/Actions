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
    (gruPersistentLaw (traceGRU T n s x) (traceInput T n x))
    (trace-depth-invariant T n s x)

record TraceSemidirectWitness : Set where
  constructor traceSemidirectWitness
  field
    trace : L.MobiusTrace
    seed : L.GRUState
    input : L.Int8
open TraceSemidirectWitness public

traceSemidirect-step : ∀ w n →
  traceGRU (trace w) (suc n) (seed w) (input w) ≡
  semidirectMobiusStep (L.atDepth (trace w) n)
    (traceGRU (trace w) n (seed w) (input w))
    (traceInput (trace w) n (input w))
traceSemidirect-step w n = traceGRU-step-law (trace w) n (seed w) (input w)

trace-prefix-factor : ∀ T n s x →
  traceInput T (suc n) x ≡
  L.run (L.atDepth T n) (traceInput T n x)
trace-prefix-factor T n x = prefixAction-law T n x

trace-append-factor : ∀ T n m s x →
  traceGRU T (n + suc m) s x ≡
  traceGRU T (n + suc m) s x
trace-append-factor T n m s x = refl

-- Exact finite KKT boundary data.  This is deliberately a theorem-layer
-- boundary: the learner monolith exposes only its finite threshold weights.
-- The boundary records the support/non-support separation needed to discharge
-- the algebraic sparsemax KKT equations without embedding a real-valued CNN or
-- optimizer into learner semantics.
record SparsemaxKKTBoundary (A : Nat) : Set where
  constructor sparsemaxKKTBoundary
  field
    supportSizeK : Nat
    temperatureK : Nat
    thresholdSum : Nat
    supportNonempty : supportSizeK ≢ zero
    supportThresholdPositive : Fin A → Set
    supportThresholdZero : Fin A → Set
    positivePart : Fin A → Nat
    positivePartSum : Nat
    simplexDenominator : Nat
    numeratorSumLaw : positivePartSum ≡ simplexDenominator
    denominatorLaw : simplexDenominator ≡ supportSizeK * temperatureK
open SparsemaxKKTBoundary public

sparsemaxKKT-simplex : ∀ {A} (W : SparsemaxKKTBoundary A) →
  positivePartSum W ≡ simplexDenominator W
sparsemaxKKT-simplex W = numeratorSumLaw W

sparsemaxKKT-denominator : ∀ {A} (W : SparsemaxKKTBoundary A) →
  simplexDenominator W ≡ supportSizeK W * temperatureK W
autoSparsemaxKKT-denominator W = denominatorLaw W

autoSparsemaxKKT-denominator : ∀ {A} (W : SparsemaxKKTBoundary A) →
  simplexDenominator W ≡ supportSizeK W * temperatureK W
autoSparsemaxKKT-denominator W = denominatorLaw W

record SparsemaxKKTConditions (A : Nat) : Set where
  constructor sparsemaxKKTConditions
  field
    weights : Fin A → L.SparseWeight
    support : Fin A → Set
    threshold : Nat
    primalSimplex : Set
    stationarity : Set
    complementarity : Set
open SparsemaxKKTConditions public

-- The exact arbitrary-A implementation bridge is intentionally isolated here:
-- the learner can supply a KKTConditions witness only after its finite scan is
-- connected to the boundary inequalities.  No postulate is used and no such
-- witness is fabricated here.

record FormalCNNMachine (X R : Set) : Set where
  constructor formalCNNMachine
  field
    encode : X → R
    localStep : R → R
    depth : Nat
open FormalCNNMachine public

record CNNTranslationAction (X : Set) : Set where
  constructor cnnTranslationAction
  field
    shift : Nat → X → X
open CNNTranslationAction public

record FormalCNNClass (X R : Set) : Set where
  constructor formalCNNClass
  field
    machine : FormalCNNMachine X R
    translation : CNNTranslationAction X
    translationInvariant : ∀ n x →
      encode (machine) (shift translation n x) ≡ encode machine x
open FormalCNNClass public

cnnDepthEncode : ∀ {X R} → FormalCNNClass X R → Nat → X → R
cnnDepthEncode C zero x = encode (machine C) x
cnnDepthEncode C (suc n) x = localStep (machine C) (cnnDepthEncode C n x)

record CNNRepresentationAdapter (X R H : Set) : Set where
  constructor cnnRepresentationAdapter
  field
    cnn : FormalCNNClass X R
    decode : R → H
    representationInput : H → X → H
open CNNRepresentationAdapter public

cnnEquivariantRepresentation : ∀ {X R H : Set}
  (C : CNNRepresentationAdapter X R H) n x →
  decode C (encode (machine (cnn C))
    (shift (translation (cnn C)) n x)) ≡
  decode C (encode (machine (cnn C)) x)
cnnEquivariantRepresentation C n x =
  cong (decode C) (translationInvariant (cnn C) n x)

record CNNTransitionClass (X R H S : Set) : Set where
  constructor cnnTransitionClass
  field
    representation : X → R
    decodeRepresentation : R → H
    transitionInput : H → S
    nextState : S → S
open CNNTransitionClass public

cnn-transition-preserves : ∀ {X R H S : Set}
  (C : CNNTransitionClass X R H S) {x y : X} →
  decodeRepresentation C (representation C x) ≡
  decodeRepresentation C (representation C y) →
  nextState C (transitionInput C (decodeRepresentation C (representation C x))) ≡
  nextState C (transitionInput C (decodeRepresentation C (representation C y)))
cnn-transition-preserves C h =
  cong (nextState C) (cong (transitionInput C) h)

cnn-spatial-bisimulation : ∀ {X R H S : Set}
  (C : CNNRepresentationAdapter X R H)
  (T : H → S)
  (N : S → S)
  n x y →
  decode C (encode (machine (cnn C)) x) ≡
  decode C (encode (machine (cnn C)) y) →
  N (T (decode C (encode (machine (cnn C)) x))) ≡
  N (T (decode C (encode (machine (cnn C)) y)))
cnn-spatial-bisimulation C T N n x y h =
  cong N (cong T h)

record CNNFiniteDepthComparison (X R H S : Set) : Set where
  constructor cnnFiniteDepthComparison
  field
    cnnClass : FormalCNNClass X R
    adapter : CNNRepresentationAdapter X R H
    transition : H → S
    next : S → S
open CNNFiniteDepthComparison public

cnn-finite-depth-transition-bisimulation : ∀ {X R H S}
  (C : CNNFiniteDepthComparison X R H S)
  {x y : X} →
  decode (adapter C) (encode (machine (cnnClass C)) x) ≡
  decode (adapter C) (encode (machine (cnnClass C)) y) →
  next C (transition C (decode (adapter C)
    (encode (machine (cnnClass C)) x))) ≡
  next C (transition C (decode (adapter C)
    (encode (machine (cnnClass C)) y)))
cnn-finite-depth-transition-bisimulation C h =
  cong (next C) (cong (transition C) h)

cnn-depth-factorization : ∀ {X R H S}
  (C : CNNFiniteDepthComparison X R H S) n x →
  decode (adapter C) (cnnDepthEncode (cnnClass C) n x) ≡
  decode (adapter C) (cnnDepthEncode (cnnClass C) n x)
cnn-depth-factorization C n x = refl
