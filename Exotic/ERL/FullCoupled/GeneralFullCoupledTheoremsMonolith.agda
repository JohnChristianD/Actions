{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_<_ ; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m+n)
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

clock-lower-bound : ∀ {A} K n s r →
  L.clock s ≤ L.clock (L.iterateLearner K n s r)
clock-lower-bound K n s r =
  subst
    (λ z → L.clock s ≤ z)
    (sym (iterateLearner-clock K n s r))
    (m≤m+n (L.clock s) n)

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

trace-prefix-factor : ∀ T n x →
  traceInput T (suc n) x ≡
  L.run (L.atDepth T n) (traceInput T n x)
trace-prefix-factor T n x = prefixAction-law T n x

traceStep : L.MobiusTrace → Nat → L.GRUState → L.Int8 → L.GRUState
traceStep T n s x = semidirectMobiusStep (L.atDepth T n) s (traceInput T n x)

traceIterate : L.MobiusTrace → Nat → L.GRUState → L.Int8 → L.GRUState
traceIterate T zero s x = s
traceIterate T (suc n) s x = traceStep T n (traceIterate T n s x) x

traceGRU-unbounded : ∀ T n s x →
  traceGRU T n s x ≡ traceIterate T n s x
traceGRU-unbounded T zero s x = refl
traceGRU-unbounded T (suc n) s x =
  trans
    (traceGRU-step-law T n s x)
    (cong
      (λ st → L.gruStep st (L.run (L.atDepth T n) (traceInput T n x)))
      (traceGRU-unbounded T n s x))

trace-depth-recurrence : ∀ T n s x →
  traceGRU T (suc n) s x ≡
  traceStep T n (traceGRU T n s x) x
trace-depth-recurrence T n s x = traceGRU-step-law T n s x

trace-prefix-semidirect-composition : ∀ T n m s x →
  semidirectMobiusStep
    (L.composeMobius (L.prefixAction T n) (L.prefixAction T m))
    s x ≡
  L.gruStep s
    (L.run (L.prefixAction T n)
      (L.run (L.prefixAction T m) x))
trace-prefix-semidirect-composition T n m s x = refl

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
sparsemaxKKT-denominator W = denominatorLaw W

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

record StandardCNNStack (R : Set) : Set where
  constructor standardCNNStack
  field
    layer : Nat → R → R
    shift : Nat → R → R
    layer-equivariant : ∀ d n x →
      layer d (shift n x) ≡ shift n (layer d x)
open StandardCNNStack public

iterateLayers : ∀ {R : Set} → (Nat → R → R) → Nat → R → R
iterateLayers layer zero x = x
iterateLayers layer (suc n) x = layer n (iterateLayers layer n x)

standardCNN-depth-equivariant : ∀ {R : Set}
  (C : StandardCNNStack R) d n x →
  iterateLayers (layer C) d (shift C n x) ≡
  shift C n (iterateLayers (layer C) d x)
standardCNN-depth-equivariant C zero n x = refl
standardCNN-depth-equivariant C (suc d) n x =
  trans
    (cong (layer C) (standardCNN-depth-equivariant C d n x))
    (layer-equivariant C d n (iterateLayers (layer C) d x))

record CNNLearnerComparison (X R H : Set) : Set where
  constructor cnnLearnerComparison
  field
    input : X → R
    decodeState : R → H
    cnnStep : R → R
    learnerStep : H → H
    commute : ∀ x →
      decodeState (cnnStep (input x)) ≡
      learnerStep (decodeState (input x))
open CNNLearnerComparison public

iterateEndo : ∀ {S : Set} → (S → S) → Nat → S → S
iterateEndo step zero s = s
iterateEndo step (suc n) s = step (iterateEndo step n s)

cnnLearner-trajectory-bisimulation : ∀ {X R H : Set}
  (C : CNNLearnerComparison X R H) n x →
  decodeState C (iterateEndo (cnnStep C) n (input C x)) ≡
  iterateEndo (learnerStep C) n (decodeState C (input C x))
cnnLearner-trajectory-bisimulation C zero x = refl
cnnLearner-trajectory-bisimulation C (suc n) x =
  trans
    (commute C (iterateEndo (cnnStep C) n (input C x)))
    (cong (learnerStep C) (cnnLearner-trajectory-bisimulation C n x))

-- Closure surface folded into this theorem monolith.
lcbPolicy-score-law : ∀ {A} (q : L.QVec A) (c : L.CountVec A) (a : Fin A) →
  L.scoreA q c a ≡ L.int8Add (q a) (L.lcbBonus (c a))
lcbPolicy-score-law q c a = refl

generalPolicy-is-lcb-sparsemax : ∀ {A} K s →
  L.generalPolicy K s ≡
  L.sparsemaxPolicy (L.actionSpaceK K) (L.q s) (L.counts s)
generalPolicy-is-lcb-sparsemax K s = refl

learnerStep-action-closure : ∀ {A} K s r →
  L.lastAction (L.learnerStep K s r) ≡ L.generalPolicy K s
learnerStep-action-closure K s r = refl

learnerStep-q-closure : ∀ {A} K s r →
  L.q (L.learnerStep K s r) ≡
  L.updateAt (L.q s) (L.generalPolicy K s)
    (L.int8Add r
      (L.munchausenSignal
        (L.mode K)
        (L.sparsemaxWeight
          (L.actionSpaceK K) (L.q s) (L.counts s)
          (L.generalPolicy K s))))
learnerStep-q-closure K s r = refl

learnerStep-count-closure : ∀ {A} K s r →
  L.counts (L.learnerStep K s r) ≡
  L.incAt (L.counts s) (L.generalPolicy K s)
learnerStep-count-closure K s r = refl

iterateLearner-zero-closure : ∀ {A} K s r →
  L.iterateLearner K zero s r ≡ s
iterateLearner-zero-closure K s r = refl

iterateLearner-suc-closure : ∀ {A} K n s r →
  L.iterateLearner K (suc n) s r ≡
  L.learnerStep K (L.iterateLearner K n s r) r
iterateLearner-suc-closure K n s r = refl

prefixAction-zero-closure : ∀ T →
  L.prefixAction T zero ≡ L.identityMobius
prefixAction-zero-closure T = refl

prefixAction-suc-closure : ∀ T n →
  L.prefixAction T (suc n) ≡
  L.composeMobius (L.atDepth T n) (L.prefixAction T n)
prefixAction-suc-closure T n = refl

semidirectCompose-mobius-closure : ∀ f g s x →
  semidirectMobiusStep (L.composeMobius f g) s x ≡
  semidirectMobiusStep f s (L.run g x)
semidirectCompose-mobius-closure f g s x = refl

traceStep-closure : ∀ T n s x →
  traceStep T n s x ≡
  L.gruStep s (L.run (L.atDepth T n) (traceInput T n x))
traceStep-closure T n s x = refl

traceIterate-zero-closure : ∀ T s x →
  traceIterate T zero s x ≡ s
traceIterate-zero-closure T s x = refl

traceIterate-suc-closure : ∀ T n s x →
  traceIterate T (suc n) s x ≡
  traceStep T n (traceIterate T n s x) x
traceIterate-suc-closure T n s x = refl

traceIterate-depth-invariant : ∀ T n s x →
  L.gruPersistent (traceIterate T n s x) ≡ L.gruPersistent s
traceIterate-depth-invariant T zero s x = refl
traceIterate-depth-invariant T (suc n) s x =
  trans
    (gruPersistentLaw (traceIterate T n s x) (traceInput T n x))
    (traceIterate-depth-invariant T n s x)

traceGRU-depth-invariant-closure : ∀ T n s x →
  L.gruPersistent (traceGRU T n s x) ≡ L.gruPersistent s
traceGRU-depth-invariant-closure T n s x = trace-depth-invariant T n s x

weightsNumerators : ∀ {A : Nat} → (Fin A → L.SparseWeight) → L.List Nat
weightsNumerators {A} ws =
  L.mapList (λ a → L.numerator (ws a)) (L.finList A)

weightsNumeratorSum : ∀ {A : Nat} → (Fin A → L.SparseWeight) → Nat
weightsNumeratorSum ws = L.sumList (weightsNumerators ws)

record SparsemaxKKTRealization (A : Nat) : Set where
  constructor sparsemaxKKTRealization
  field
    kernel : L.ActionSpace A
    q : L.QVec A
    counts : L.CountVec A
    weights : Fin A → L.SparseWeight
    weights-law : ∀ a → weights a ≡ L.sparsemaxWeight kernel q counts a
    supportSizeK : Nat
    supportNonempty : supportSizeK ≢ zero
    denominatorK : Nat
    denominator-law : ∀ a → L.denominator (weights a) ≡ denominatorK
    simplexLaw : weightsNumeratorSum weights ≡ denominatorK
    stationarity : Fin A → Set
    complementarity : Fin A → Set
open SparsemaxKKTRealization public

sparsemaxKKT-realized-simplex : ∀ {A} (W : SparsemaxKKTRealization A) →
  weightsNumeratorSum (weights W) ≡ denominatorK W
sparsemaxKKT-realized-simplex W = simplexLaw W

sparsemaxKKT-realized-weight-law : ∀ {A} (W : SparsemaxKKTRealization A) a →
  weights W a ≡ L.sparsemaxWeight (kernel W) (q W) (counts W) a
sparsemaxKKT-realized-weight-law W a = weights-law W a

sparsemax-policy-not-attention-surface : ∀ {A} K s →
  L.generalPolicy K s ≡
  L.sparsemaxPolicy (L.actionSpaceK K) (L.q s) (L.counts s)
sparsemax-policy-not-attention-surface K s = refl

cnn-depth-closure : ∀ {R : Set}
  (C : StandardCNNStack R) d n x →
  iterateLayers (layer C) d (shift C n x) ≡
  shift C n (iterateLayers (layer C) d x)
cnn-depth-closure C d n x = standardCNN-depth-equivariant C d n x

cnn-learner-trajectory-closure : ∀ {X R H : Set}
  (C : CNNLearnerComparison X R H) n x →
  decodeState C (iterateEndo (cnnStep C) n (input C x)) ≡
  iterateEndo (learnerStep C) n (decodeState C (input C x))
cnn-learner-trajectory-closure C n x = cnnLearner-trajectory-bisimulation C n x
