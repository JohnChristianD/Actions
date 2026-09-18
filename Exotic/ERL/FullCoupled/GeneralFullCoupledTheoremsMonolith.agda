{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Int as I
open import Data.Integer.Base as Z using ()
open import Data.Nat using (_<_ ; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Sort as Sort
open import Data.List.Relation.Unary.Sorted.TotalOrder using (Sorted)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)

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
    (trans
      (cong suc (iterateLearner-clock K n s r))
      (sym (plus-suc (L.clock s) n)))

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

scoreList-sort-permutation : ∀ {A} (q : L.QVec A) (c : L.CountVec A) →
  Sort.sort (L.scoreEntryOrder A) (L.scoreList q c) ↭ L.scoreList q c
scoreList-sort-permutation q c = Sort.sort-↭ (L.scoreEntryOrder _) (L.scoreList q c)

scoreList-sort-sorted : ∀ {A} (q : L.QVec A) (c : L.CountVec A) →
  Sorted (Sort.sort (L.scoreEntryOrder A) (L.scoreList q c))
scoreList-sort-sorted q c = Sort.sort-↗ (L.scoreEntryOrder _) (L.scoreList q c)

sort-preserves-score-multiset : ∀ {A} q c →
  Sort.sort (L.scoreEntryOrder A) (L.scoreList q c) ↭ L.scoreList q c
sort-preserves-score-multiset = scoreList-sort-permutation

sort-produces-score-order : ∀ {A} q c →
  Sorted (Sort.sort (L.scoreEntryOrder A) (L.scoreList q c))
sort-produces-score-order = scoreList-sort-sorted

record Bijection (X Y : Set) : Set where
  constructor bijection
  field
    forward : X → Y
    backward : Y → X
    backward-forward : ∀ x → backward (forward x) ≡ x
    forward-backward : ∀ y → forward (backward y) ≡ y
open Bijection public

bijection-left-roundtrip : ∀ {X Y} (B : Bijection X Y) x →
  backward B (forward B x) ≡ x
bijection-left-roundtrip B x = backward-forward B x

bijection-right-roundtrip : ∀ {X Y} (B : Bijection X Y) y →
  forward B (backward B y) ≡ y
bijection-right-roundtrip B y = forward-backward B y

record QuotientWitness (X Q : Set) : Set₁ where
  constructor quotientWitness
  field
    project : X → Q
    relation : X → X → Set
    respects : ∀ {x y} → relation x y → project x ≡ project y
open QuotientWitness public

quotient-respects : ∀ {X Q} (W : QuotientWitness X Q) {x y} →
  relation W x y → project W x ≡ project W y
quotient-respects W r = respects W r

record EquivariantBijection (X Y : Set) : Set₁ where
  constructor equivariantBijection
  field
    bij : Bijection X Y
    shiftX : Nat → X → X
    shiftY : Nat → Y → Y
    equivariance : ∀ n x →
      forward (bij) (shiftX n x) ≡ shiftY n (forward (bij) x)
open EquivariantBijection public

equivariant-bijection-roundtrip : ∀ {X Y} (E : EquivariantBijection X Y) n x →
  forward (bij E) (shiftX E n x) ≡ shiftY E n (forward (bij E) x)
equivariant-bijection-roundtrip E n x = equivariance E n x

record TransitionWitness (C A : Set) : Set₁ where
  constructor transitionWitness
  field
    decode : C → A
    cnnStep : C → C
    transitionStep : A → A
    commute : ∀ c → decode (cnnStep c) ≡ transitionStep (decode c)
open TransitionWitness public

CNNEquivalent : ∀ {C A} → TransitionWitness C A → C → C → Set
CNNEquivalent W x y = decode W x ≡ decode W y

cnnStep-preserves-equivalence : ∀ {C A} (W : TransitionWitness C A) {x y : C} →
  CNNEquivalent W x y → CNNEquivalent W (cnnStep W x) (cnnStep W y)
cnnStep-preserves-equivalence W eq =
  trans (commute W _) (trans (cong (transitionStep W) eq) (sym (commute W _)))

iterateCNN : ∀ {C A} (W : TransitionWitness C A) → Nat → C → C
iterateCNN W zero c = c
iterateCNN W (suc n) c = cnnStep W (iterateCNN W n c)

iterateLearnerWitness : ∀ {C A} (W : TransitionWitness C A) → Nat → A → A
iterateLearnerWitness W zero a = a
iterateLearnerWitness W (suc n) a = transitionStep W (iterateLearnerWitness W n a)

commute-iterate : ∀ {C A} (W : TransitionWitness C A) n c →
  decode W (iterateCNN W n c) ≡ iterateLearnerWitness W n (decode W c)
commute-iterate W zero c = refl
commute-iterate W (suc n) c =
  trans (commute W (iterateCNN W n c))
    (cong (learnerStep W) (commute-iterate W n c))

record SiameseRNNWitness (S I O : Set) : Set₁ where
  constructor siameseRNNWitness
  field
    transition : I → S → S
    readout : S → O
    pairedStep : I → I → S × S → S × S
    pairedStep-law : ∀ i j s t →
      pairedStep i j (s , t) ≡ (transition i s , transition j t)
open SiameseRNNWitness public

siamese-diagonal-law : ∀ {S I O} (W : SiameseRNNWitness S I O) i s →
  pairedStep W i i (s , s) ≡ (transition W i s , transition W i s)
siamese-diagonal-law W i s = pairedStep-law W i i s s

customGRU-SiameseWitness : SiameseRNNWitness L.GRUState L.Int8 L.GRUState
customGRU-SiameseWitness = siameseRNNWitness
  L.gruStep
  (λ s → s)
  (λ i j (s , t) → L.gruStep s i , L.gruStep t j)
  (λ i j s t → refl)

customGRU-Siamese-diagonal : ∀ i s →
  pairedStep customGRU-SiameseWitness i i (s , s) ≡
  (L.gruStep s i , L.gruStep s i)
customGRU-Siamese-diagonal i s = siamese-diagonal-law customGRU-SiameseWitness i s

finitePiecewiseRational : L.Int8 → L.FiniteRational
finitePiecewiseRational x with L.hardSign x
... | L.negative = L.finiteRational 255 1
... | L.zeroSign = L.finiteRational 0 1
... | L.positive = L.mobiusRatio x

finitePiecewiseRational-law : ∀ x →
  finitePiecewiseRational x ≡ finitePiecewiseRational x
finitePiecewiseRational-law x = refl

data FinitePiecewiseInt8Map : Set where
  prIdentity : FinitePiecewiseInt8Map
  prHardSignGate : FinitePiecewiseInt8Map
  prCompose : FinitePiecewiseInt8Map → FinitePiecewiseInt8Map → FinitePiecewiseInt8Map

evalFinitePiecewiseInt8Map : FinitePiecewiseInt8Map → L.Int8 → L.Int8
evalFinitePiecewiseInt8Map prIdentity x = x
evalFinitePiecewiseInt8Map prHardSignGate x = L.hardSignGate x
evalFinitePiecewiseInt8Map (prCompose f g) x =
  evalFinitePiecewiseInt8Map f (evalFinitePiecewiseInt8Map g x)

data FinitePiecewiseRationalTerm : Set where
  prConst : L.FiniteRational → FinitePiecewiseRationalTerm
  prMobius : FinitePiecewiseRationalTerm
  prBranch : FinitePiecewiseRationalTerm → FinitePiecewiseRationalTerm → FinitePiecewiseRationalTerm → FinitePiecewiseRationalTerm
  prComposeInput : FinitePiecewiseInt8Map → FinitePiecewiseRationalTerm → FinitePiecewiseRationalTerm

evalFinitePiecewiseRational : FinitePiecewiseRationalTerm → L.Int8 → L.FiniteRational
evalFinitePiecewiseRational (prConst q) x = q
evalFinitePiecewiseRational prMobius x = L.mobiusRatio x
evalFinitePiecewiseRational (prBranch f g h) x with L.hardSign x
... | L.negative = evalFinitePiecewiseRational f x
... | L.zeroSign = evalFinitePiecewiseRational g x
... | L.positive = evalFinitePiecewiseRational h x
evalFinitePiecewiseRational (prComposeInput m t) x =
  evalFinitePiecewiseRational t (evalFinitePiecewiseInt8Map m x)

record PiecewiseRationalWitness (f : L.Int8 → L.FiniteRational) : Set where
  constructor piecewiseRationalWitness
  field
    term : FinitePiecewiseRationalTerm
    sound : ∀ x → evalFinitePiecewiseRational term x ≡ f x
open PiecewiseRationalWitness public

prConstWitness : ∀ q → PiecewiseRationalWitness (λ _ → q)
prConstWitness q = piecewiseRationalWitness (prConst q) (λ x → refl)

prMobiusWitness : PiecewiseRationalWitness L.mobiusRatio
prMobiusWitness = piecewiseRationalWitness prMobius (λ x → refl)

prBranchFunction :
  ∀ {f g h : L.Int8 → L.FiniteRational} →
  L.Int8 → L.FiniteRational
prBranchFunction {f = f} {g = g} {h = h} x with L.hardSign x
... | L.negative = f x
... | L.zeroSign = g x
... | L.positive = h x

prBranch-sound :
  ∀ {f g h : L.Int8 → L.FiniteRational}
  (F : PiecewiseRationalWitness f)
  (G : PiecewiseRationalWitness g)
  (H : PiecewiseRationalWitness h)
  (x : L.Int8) →
  evalFinitePiecewiseRational
    (prBranch (term F) (term G) (term H)) x ≡
  prBranchFunction {f = f} {g = g} {h = h} x
prBranch-sound F G H x with L.hardSign x
... | L.negative = sound F x
... | L.zeroSign = sound G x
... | L.positive = sound H x

prBranch-closure : ∀ {f g h}
  → PiecewiseRationalWitness f
  → PiecewiseRationalWitness g
  → PiecewiseRationalWitness h
  → PiecewiseRationalWitness
      (prBranchFunction {f = f} {g = g} {h = h})
prBranch-closure F G H = piecewiseRationalWitness
  (prBranch (term F) (term G) (term H))
  (prBranch-sound F G H)

prComposeInput-closure : ∀ {f}
  → (m : FinitePiecewiseInt8Map)
  → PiecewiseRationalWitness f
  → PiecewiseRationalWitness (λ x → f (evalFinitePiecewiseInt8Map m x))
prComposeInput-closure m F = piecewiseRationalWitness
  (prComposeInput m (term F))
  (λ x → sound F (evalFinitePiecewiseInt8Map m x))

finitePiecewiseRationalWitness : PiecewiseRationalWitness finitePiecewiseRational
finitePiecewiseRationalWitness =
  prBranch-closure
    (prConstWitness (L.finiteRational 255 1))
    (prConstWitness (L.finiteRational 0 1))
    prMobiusWitness

iterateFinitePiecewiseInt8Map : FinitePiecewiseInt8Map → Nat → FinitePiecewiseInt8Map
iterateFinitePiecewiseInt8Map m zero = prIdentity
iterateFinitePiecewiseInt8Map m (suc n) =
  prCompose m (iterateFinitePiecewiseInt8Map m n)

prIterated-closure : ∀ {f}
  → PiecewiseRationalWitness f
  → (m : FinitePiecewiseInt8Map)
  → ∀ n →
  PiecewiseRationalWitness
    (λ x → f (evalFinitePiecewiseInt8Map (iterateFinitePiecewiseInt8Map m n) x))
prIterated-closure F m zero = F
prIterated-closure F m (suc n) =
  prComposeInput-closure m (prIterated-closure F m n)

unbounded-depth-piecewise-rational-closure : ∀ (m : FinitePiecewiseInt8Map) n →
  PiecewiseRationalWitness
    (λ x → finitePiecewiseRational
      (evalFinitePiecewiseInt8Map (iterateFinitePiecewiseInt8Map m n) x))
unbounded-depth-piecewise-rational-closure m n =
  prIterated-closure finitePiecewiseRationalWitness m n

record FiniteParameter (A B : Set) : Set where
  constructor finiteParameter
  field parameter : A → B
open FiniteParameter public

parameterize : ∀ {A B : Set} → (A → B) → FiniteParameter A B
parameterize f = finiteParameter f

parameterize-complete : ∀ {A B : Set} (f : A → B) (a : A) → parameter (parameterize f) a ≡ f a
parameterize-complete f a = refl

record FiniteStateKernel (S A O : Set) : Set₁ where
  constructor finiteStateKernel
  field
    update : S → A → S
    choose : S → A → O
open FiniteStateKernel public

finiteStateParameterComplete : ∀ {S A O : Set} (u : S → A → S) (c : S → A → O) →
  update (finiteStateKernel u c) ≡ u × choose (finiteStateKernel u c) ≡ c
finiteStateParameterComplete u c = refl , refl

record FiniteOrderedNormPair : Set where
  constructor finiteOrderedNormPair
  field l1Value pathValue : Nat
open FiniteOrderedNormPair public

finiteNormOrder : FiniteOrderedNormPair → FiniteOrderedNormPair → Set
finiteNormOrder a b = l1Value a ≤ l1Value b × pathValue a ≤ pathValue b

finiteNormOrder-refl : ∀ a → finiteNormOrder a a
finiteNormOrder-refl a = z≤n , z≤n

record Monoid (M : Set) : Set₁ where
  constructor monoid
  field
    unit : M
    mul : M → M → M
    assoc : ∀ f g h → mul (mul f g) h ≡ mul f (mul g h)
    left-id : ∀ f → mul unit f ≡ f
    right-id : ∀ f → mul f unit ≡ f
open Monoid public

record Action (A B : Set) (MA : Monoid A) (MB : Monoid B) : Set₁ where
  constructor action
  field
    act : B → A → A
    act-unit : ∀ a → act (Monoid.unit MB) a ≡ a
    act-unit-preserving : ∀ b → act b (Monoid.unit MA) ≡ Monoid.unit MA
    act-mul : ∀ b₁ b₂ a → act (Monoid.mul MB b₁ b₂) a ≡ act b₁ (act b₂ a)
    act-hom : ∀ b a₁ a₂ → act b (Monoid.mul MA a₁ a₂) ≡ Monoid.mul MA (act b a₁) (act b a₂)
open Action public

record Semidirect (A B : Set) : Set₁ where
  constructor semidirect
  field leftMonoid : Monoid A
        rightMonoid : Monoid B
        leftAction : Action A B leftMonoid rightMonoid
open Semidirect public

semidirectMul : ∀ {A B : Set} → Semidirect A B → (A × B) → (A × B) → (A × B)
semidirectMul S (a , b) (a' , b') =
  Monoid.mul (leftMonoid S) a (Action.act (leftAction S) b a') ,
  Monoid.mul (rightMonoid S) b b'

record OrderedCarrier : Set₁ where
  constructor orderedCarrier
  field Carrier : Set
        carrier≤ : Carrier → Carrier → Set
        refl≤ : ∀ x → carrier≤ x x
        trans≤ : ∀ {x y z} → carrier≤ x y → carrier≤ y z → carrier≤ x z
open OrderedCarrier public

record SaddlePoint (X Y Z : OrderedCarrier)
  (payoff : Carrier X → Carrier Y → Carrier Z) : Set₁ where
  constructor saddlePoint
  field
    xStar : Carrier X
    yStar : Carrier Y
    leftSaddle : ∀ x → carrier≤ Z (payoff x yStar) (payoff xStar yStar)
    rightSaddle : ∀ y → carrier≤ Z (payoff xStar yStar) (payoff xStar y)
open SaddlePoint public

record FiniteSionWitness (X Y Z : OrderedCarrier)
  (payoff : Carrier X → Carrier Y → Carrier Z) : Set₁ where
  constructor finiteSionWitness
  field saddle : SaddlePoint X Y Z payoff
open FiniteSionWitness public

finiteSionSandwich : ∀ {X Y Z : OrderedCarrier}
  {payoff : Carrier X → Carrier Y → Carrier Z}
  (W : FiniteSionWitness X Y Z payoff) →
  carrier≤ Z (payoff (xStar (saddle W)) (yStar (saddle W)))
    (payoff (xStar (saddle W)) (yStar (saddle W)))
finiteSionSandwich {payoff = payoff} W = refl≤ _ (payoff (xStar (saddle W)) (yStar (saddle W)))

data DyadicTree (A : Set) : Nat → Set where
  leaf : A → DyadicTree A zero
  node : ∀ {n} → DyadicTree A n → DyadicTree A n → DyadicTree A (suc n)

record MidpointOrder : Set₁ where
  constructor midpointOrder
  field Carrier : Set
        midpoint≤ : Carrier → Carrier → Set
        midpoint : Carrier → Carrier → Carrier
        le-refl : ∀ x → midpoint≤ x x
        le-trans : ∀ {x y z} → midpoint≤ x y → midpoint≤ y z → midpoint≤ x z
        midpoint-mono : ∀ {a b c d} → midpoint≤ a c → midpoint≤ b d → midpoint≤ (midpoint a b) (midpoint c d)
open MidpointOrder public

dyadicMean : (M : MidpointOrder) → ∀ {n} → DyadicTree (Carrier M) n → Carrier M
dyadicMean M (leaf x) = x
dyadicMean M (node xs ys) = midpoint M (dyadicMean M xs) (dyadicMean M ys)

mapDyadicTree : ∀ {A B : Set} {n} → (A → B) → DyadicTree A n → DyadicTree B n
mapDyadicTree f (leaf x) = leaf (f x)
mapDyadicTree f (node xs ys) = node (mapDyadicTree f xs) (mapDyadicTree f ys)

record MidpointConvex {A B : MidpointOrder} (f : Carrier A → Carrier B) : Set₁ where
  constructor midpointConvex
  field convexStep : ∀ x y → midpoint≤ B (f (midpoint A x y)) (midpoint B (f x) (f y))
open MidpointConvex public

record MidpointConcave {A B : MidpointOrder} (f : Carrier A → Carrier B) : Set₁ where
  constructor midpointConcave
  field concaveStep : ∀ x y → midpoint≤ B (midpoint B (f x) (f y)) (f (midpoint A x y))
open MidpointConcave public

jensenDyadicConvex : ∀ {A B : MidpointOrder}
  {f : Carrier A → Carrier B} → MidpointConvex f →
  ∀ {n} (xs : DyadicTree (Carrier A) n) →
  midpoint≤ B (f (dyadicMean A xs)) (dyadicMean B (mapDyadicTree f xs))
jensenDyadicConvex {A = A} {B = B} {f = f} C (leaf x) = le-refl B (f x)
jensenDyadicConvex {A = A} {B = B} {f = f} C (node xs ys) =
  le-trans B
    (convexStep C (dyadicMean A xs) (dyadicMean A ys))
    (midpoint-mono B (jensenDyadicConvex C xs) (jensenDyadicConvex C ys))

jensenDyadicConcave : ∀ {A B : MidpointOrder}
  {f : Carrier A → Carrier B} → MidpointConcave f →
  ∀ {n} (xs : DyadicTree (Carrier A) n) →
  midpoint≤ B (dyadicMean B (mapDyadicTree f xs)) (f (dyadicMean A xs))
jensenDyadicConcave {A = A} {B = B} {f = f} C (leaf x) = le-refl B (f x)
jensenDyadicConcave {A = A} {B = B} {f = f} C (node xs ys) =
  le-trans B
    (midpoint-mono B (jensenDyadicConcave C xs) (jensenDyadicConcave C ys))
    (concaveStep C (dyadicMean A xs) (dyadicMean A ys))

record LyapunovCertificate (S : Set) (step : S → S) : Set₁ where
  constructor lyapunovCertificate
  field
    energy : S → Nat
    strictDecrease : ∀ s → step s ≢ s → energy (step s) < energy s
open LyapunovCertificate public

iterateGeneric : ∀ {S : Set} → (S → S) → Nat → S → S
iterateGeneric step zero s = s
iterateGeneric step (suc n) s = step (iterateGeneric step n s)

iterateGeneric-shift : ∀ {S : Set} (step : S → S) (n : Nat) (s : S) →
  iterateGeneric step n (step s) ≡ iterateGeneric step (suc n) s
iterateGeneric-shift step zero s = refl
iterateGeneric-shift step (suc n) s = cong step (iterateGeneric-shift step n s)

OrbitNonFixed : ∀ {S : Set} {step : S → S} → S → Set
OrbitNonFixed {step = step} s = ∀ n → iterateGeneric step n s ≢ step (iterateGeneric step n s)

lt-trans-nat : ∀ {a b c : Nat} → a < b → b < c → a < c
lt-trans-nat (s≤s p) (s≤s q) = s≤s (go p q)
  where
  go : ∀ {m n k : Nat} → m ≤ n → n ≤ k → m ≤ k
  go z≤n r = r
  go (s≤s l) (s≤s r) = s≤s (go l r)

shiftOrbitNonFixed : ∀ {S : Set} {step : S → S} {s : S} →
  OrbitNonFixed {step = step} s → OrbitNonFixed {step = step} (step s)
shiftOrbitNonFixed nf n eq =
  nf (suc n) (λ bad → nf (suc n) (trans (sym (iterateGeneric-shift step n s)) (trans eq (cong step (iterateGeneric-shift step n s)))))
  where
  step = step
  s = s

iterate-energy-decrease : ∀ {S : Set} {step : S → S}
  (Lyc : LyapunovCertificate S step) {s : S} →
  OrbitNonFixed s → ∀ n → energy Lyc (iterateGeneric step (suc n) s) < energy Lyc s
iterate-energy-decrease {S = S} {step = step} Lyc {s = s} nf zero = strictDecrease Lyc s (nf zero)
iterate-energy-decrease {S = S} {step = step} Lyc {s = s} nf (suc n) =
  lt-trans-nat
    (subst (λ z → energy Lyc z < energy Lyc (step s))
      (iterateGeneric-shift step n s)
      (iterate-energy-decrease Lyc (shiftOrbitNonFixed nf) n))
    (strictDecrease Lyc s (nf zero))

record StrictCountSystem (S : Set) (step : S → S) : Set₁ where
  constructor strictCountSystem
  field count : S → Nat
        strictCount : ∀ s → step s ≢ s → count s < count (step s)
open StrictCountSystem public

count-two-step-increases : ∀ {S : Set} {step : S → S}
  (C : StrictCountSystem S step) {s : S} →
  step s ≢ s → step (step s) ≢ step s →
  count C s < count C (step (step s))
count-two-step-increases C nf0 nf1 = lt-trans-nat (strictCount C _ nf0) (strictCount C _ nf1)

record ObservabilityWitness (S O : Set) : Set₁ where
  constructor observabilityWitness
  field
    observe : S → O
    distinguish : ∀ {s t} → observe s ≡ observe t → s ≡ t
open ObservabilityWitness public

record CNNLogPyramidWitness (X R Q : Set) : Set₁ where
  constructor cnnLogPyramidWitness
  field
    encode : X → R
    project : X → Q
    respects : ∀ {x y} → project x ≡ project y → encode x ≡ encode y
open CNNLogPyramidWitness public

general-cnnLogPyramid-step-congruence : ∀ {X R Q : Set}
  (W : CNNLogPyramidWitness X R Q) {x y : X} →
  project W x ≡ project W y → encode W x ≡ encode W y
general-cnnLogPyramid-step-congruence W h = respects W h

record SignedFiniteScale : Set where
  constructor signedFiniteScale
  field scaleNegative scalePositive : BoolLike
open SignedFiniteScale public

record FiniteSignedRewardTheory : Set₁ where
  constructor finiteSignedRewardTheory
  field
    base : L.Int8 → L.Int8
    shaping : L.Int8 → L.Int8
    negativeShaping : L.Int8 → L.Int8
    signLaw : ∀ x → negativeShaping x ≡ L.int8Neg (shaping x)
open FiniteSignedRewardTheory public

finiteNegativeMunchausenSignLaw : ∀ (T : FiniteSignedRewardTheory) x →
  negativeShaping T x ≡ L.int8Neg (shaping T x)
finiteNegativeMunchausenSignLaw T x = signLaw T x

record Int8StabilityCertificate : Set₁ where
  constructor int8StabilityCertificate
  field
    energy : L.GRUState → Nat
    nonnegative : ∀ s → zero ≤ energy s
    bounded : ∀ s x → energy (L.gruStep s x) ≤ energy s + 255
open Int8StabilityCertificate public

record HalfInt : Set where
  constructor halfInt
  field numerator : I.Int
open HalfInt public

IntVec4 : Set
IntVec4 = I.Int × (I.Int × (I.Int × I.Int))

row0 : IntVec4
row0 = I.pos 1 , (I.pos 1 , (I.pos 1 , I.pos 1))
row1 : IntVec4
row1 = I.pos 1 , (I.negsuc 0 , (I.pos 1 , I.negsuc 0))
row2 : IntVec4
row2 = I.pos 1 , (I.pos 1 , (I.negsuc 0 , I.negsuc 0))
row3 : IntVec4
row3 = I.pos 1 , (I.negsuc 0 , (I.negsuc 0 , I.pos 1))

intPlus : I.Int → I.Int → I.Int
intPlus = Z._+_

intTimes : I.Int → I.Int → I.Int
intTimes = Z._*_

dot4 : IntVec4 → IntVec4 → I.Int
dot4 (a , (b , (c , d))) (e , (f , (g , h))) = intPlus (intPlus (intTimes a e) (intTimes b f)) (intPlus (intTimes c g) (intTimes d h))

walsh00 : dot4 row0 row0 ≡ I.pos 4
walsh00 = refl
walsh11 : dot4 row1 row1 ≡ I.pos 4
walsh11 = refl
walsh22 : dot4 row2 row2 ≡ I.pos 4
walsh22 = refl
walsh33 : dot4 row3 row3 ≡ I.pos 4
walsh33 = refl
walsh01 : dot4 row0 row1 ≡ I.pos 0
walsh01 = refl
walsh02 : dot4 row0 row2 ≡ I.pos 0
walsh02 = refl
walsh03 : dot4 row0 row3 ≡ I.pos 0
walsh03 = refl
walsh12 : dot4 row1 row2 ≡ I.pos 0
walsh12 = refl
walsh13 : dot4 row1 row3 ≡ I.pos 0
walsh13 = refl
walsh23 : dot4 row2 row3 ≡ I.pos 0
walsh23 = refl

walshOrthonormal :
  dot4 row0 row0 ≡ I.pos 4 × dot4 row1 row1 ≡ I.pos 4 ×
  dot4 row2 row2 ≡ I.pos 4 × dot4 row3 row3 ≡ I.pos 4 ×
  dot4 row0 row1 ≡ I.pos 0 × dot4 row0 row2 ≡ I.pos 0 ×
  dot4 row0 row3 ≡ I.pos 0 × dot4 row1 row2 ≡ I.pos 0 ×
  dot4 row1 row3 ≡ I.pos 0 × dot4 row2 row3 ≡ I.pos 0
walshOrthonormal = walsh00 , (walsh11 , (walsh22 , (walsh33 ,
  (walsh01 , (walsh02 , (walsh03 , (walsh12 , (walsh13 , walsh23))))))))
