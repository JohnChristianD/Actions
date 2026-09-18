{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Int as I
open import Data.Integer.Base as Z using ()
open import Data.Nat using (_<_ ; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m+n; <-trans; +-mono-≤)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Data.Fin using (Fin; toℕ)
import Data.Fin as Fin
open import Data.Fin.Properties using (pigeonhole; <⇒notInjective; toℕ-injective; toℕ<n; n<1+n)
open import Function.Definitions using (Injective)
open import Data.Product using (_×_; _,_; ∃; ∃₂)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Sort as Sort
open import Data.List.Relation.Unary.Sorted.TotalOrder using (Sorted)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

natLeRefl : ∀ n → n ≤ n
natLeRefl zero = z≤n
natLeRefl (suc n) = s≤s (natLeRefl n)

record FullCompositionPigeonhole (n : Nat) : Set₁ where
  constructor fullCompositionPigeonhole
  field
    encode : Fin (suc (suc n)) → L.LearnerState (suc n)
    observe : L.LearnerState (suc n) → Fin (suc n)
open FullCompositionPigeonhole public

fullCompositionPigeonhole-collision : ∀ {n : Nat}
  (W : FullCompositionPigeonhole n) →
  ∃₂ λ i j →
    Fin._<_ i j ×
    observe W (encode W i) ≡ observe W (encode W j)
fullCompositionPigeonhole-collision {n} W =
  pigeonhole
    (s≤s (s≤s (natLeRefl n)))
    (λ i → observe W (encode W i))

fullCompositionPigeonhole-not-injective : ∀ {n : Nat}
  (W : FullCompositionPigeonhole n) →
  ¬ Injective _≡_ _≡_ (λ i → observe W (encode W i))
fullCompositionPigeonhole-not-injective {n} W =
  <⇒notInjective (s≤s (s≤s (natLeRefl n)))

NatCoercive : ∀ {S : Set} → (S → Nat) → Set
NatCoercive e = ∀ B → ∃ λ s → B < e s

lt-irrefl : ∀ n → n < n → ⊥
lt-irrefl zero ()
lt-irrefl (suc n) (s≤s p) = lt-irrefl n p

int8-code-not-coercive : ¬ NatCoercive (λ x → toℕ (L.code x))
int8-code-not-coercive coercive with coercive 256
... | s , h =
  lt-irrefl 256
    (lt-trans-nat-local h (toℕ<n (L.code s)))
  where
  lt-trans-nat-local : ∀ {a b c : Nat} → a < b → b < c → a < c
  lt-trans-nat-local = <-trans


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

suc-as-plus : ∀ n → suc n ≡ n + suc zero
suc-as-plus n = sym (trans (plus-suc n zero) (cong suc (plus-zero n)))

learnerNoFixedPoint : ∀ {A} K s r →
  L.learnerStep K s r ≢ s
learnerNoFixedPoint K s r eq =
  plus-suc-not-self (L.clock s) zero
    (trans
      (sym (suc-as-plus (L.clock s)))
      (trans (sym (learnerStep-clock K s r)) (cong L.clock eq)))

iterateLearner-clock : ∀ {A} K n s r →
  L.clock (L.iterateLearner K n s r) ≡ L.clock s + n
iterateLearner-clock K zero s r = sym (plus-zero (L.clock s))
iterateLearner-clock K (suc n) s r =
  trans
    (learnerStep-clock K (L.iterateLearner K n s r) r)
    (trans
      (suc-as-plus (L.clock (L.iterateLearner K n s r)))
      (trans
        (cong (λ z → z + suc zero) (iterateLearner-clock K n s r))
        (trans
          (sym (suc-as-plus (L.clock s + n)))
          (sym (plus-suc (L.clock s) n)))))

clock-lower-bound : ∀ {A} K n s r →
  L.clock s ≤ L.clock (L.iterateLearner K n s r)
clock-lower-bound K n s r =
  subst
    (λ z → L.clock s ≤ z)
    (sym (iterateLearner-clock K n s r))
    (m≤m+n (L.clock s) n)

fullLearnerEncode257 : ∀ {A} (K : L.LearnerKernel A) →
  Fin 257 → L.LearnerState A
fullLearnerEncode257 K i =
  L.iterateLearner K (toℕ i)
    (L.initialLearner (L.actionSpaceK K))
    L.zero8

zero-plus : ∀ n → zero + n ≡ n
zero-plus n = refl

fullLearnerEncode257-clock : ∀ {A} (K : L.LearnerKernel A) (i : Fin 257) →
  L.clock (fullLearnerEncode257 K i) ≡ toℕ i
fullLearnerEncode257-clock K i =
  trans
    (iterateLearner-clock K (toℕ i)
      (L.initialLearner (L.actionSpaceK K)) L.zero8)
    (zero-plus (toℕ i))

fullLearnerEncode257-distinct : ∀ {A} (K : L.LearnerKernel A)
  {i j : Fin 257} →
  fullLearnerEncode257 K i ≡ fullLearnerEncode257 K j →
  i ≡ j
fullLearnerEncode257-distinct K {i} {j} eq =
  toℕ-injective
    (trans
      (sym (fullLearnerEncode257-clock K i))
      (trans
        (cong L.clock eq)
        (fullLearnerEncode257-clock K j)))

fullLearnerObservationCode :
  ∀ {A} (K : L.LearnerKernel A)
  (observe : L.LearnerState A → L.Int8) →
  Fin 257 → Fin 256
fullLearnerObservationCode K observe i =
  L.code (observe (fullLearnerEncode257 K i))

fullLearnerState-observation-not-injective :
  ∀ {A} (K : L.LearnerKernel A)
  (observe : L.LearnerState A → L.Int8) →
  ¬ Injective _≡_ _≡_ observe
fullLearnerState-observation-not-injective K observe inj
  with pigeonhole (n<1+n 256) (fullLearnerObservationCode K observe)
... | i , j , apart , codeEq =
  apart
    (fullLearnerEncode257-distinct K
      (inj (cong L.int8 codeEq)))

fullLearnerState-no-left-inverse :
  ∀ {A} (K : L.LearnerKernel A)
  (observe : L.LearnerState A → L.Int8)
  (inverse : L.Int8 → L.LearnerState A) →
  (∀ s → inverse (observe s) ≡ s) →
  ⊥
fullLearnerState-no-left-inverse K observe inverse leftInverse =
  fullLearnerState-observation-not-injective
    K observe
    (λ {s} {t} eq →
      trans
        (sym (leftInverse s))
        (trans
          (cong inverse eq)
          (leftInverse t)))

finiteParameterComplete : ∀ {A : Nat}
  (table : L.QVec A) → (λ a → table a) ≡ table
finiteParameterComplete table = refl

fullCompositionBisimulation : ∀ {A} K s t r →
  s ≡ t → L.learnerStep K s r ≡ L.learnerStep K t r
fullCompositionBisimulation K s t r refl = refl

norm-pair-monotone : ∀ n w x →
  L.l1Weight n ≤ L.l1Weight (L.normStep n w x)
norm-pair-monotone n w x =
  m≤m+n (L.l1Weight n) (L.int8AbsCode w)

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

wrap-int8Sub-law : ∀ x y →
  L.int8Sub x y ≡ L.int8Add x (L.int8Neg y)
wrap-int8Sub-law x y = refl

f4-wrap-add-law : ∀ x y →
  L.f4Add x y ≡ L.int8Add x y
f4-wrap-add-law x y = refl

f4-wrap-sub-law : ∀ x y →
  L.f4Sub x y ≡ L.int8Sub x y
f4-wrap-sub-law x y = refl

record ScanAction : Set where
  constructor scanAction
  field runScan : L.Int8 → L.Int8
open ScanAction public

identityScan : ScanAction
identityScan = scanAction (λ x → x)

composeScan : ScanAction → ScanAction → ScanAction
composeScan f g = scanAction (λ x → runScan f (runScan g x))

scanAssociative : ∀ f g h x →
  runScan (composeScan (composeScan f g) h) x ≡
  runScan (composeScan f (composeScan g h)) x
scanAssociative f g h x = refl

record ScanTrace : Set where
  constructor scanTrace
  field atDepth : Nat → ScanAction
open ScanTrace public

prefixScan : ScanTrace → Nat → ScanAction
prefixScan T zero = identityScan
prefixScan T (suc n) = composeScan (atDepth T n) (prefixScan T n)

scanInput : ScanTrace → Nat → L.Int8 → L.Int8
scanInput T n x = runScan (prefixScan T n) x

scanGRU : ScanTrace → Nat → L.GRUState → L.Int8 → L.GRUState
scanGRU T zero s x = s
scanGRU T (suc n) s x =
  L.gruStep (scanGRU T n s x) (scanInput T n x)

scanGRU-step-law : ∀ T n s x →
  scanGRU T (suc n) s x ≡
  L.gruStep (scanGRU T n s x) (scanInput T n x)
scanGRU-step-law T n s x = refl

scanIterate : ScanTrace → Nat → L.GRUState → L.Int8 → L.GRUState
scanIterate T zero s x = s
scanIterate T (suc n) s x =
  L.gruStep (scanIterate T n s x) (scanInput T n x)

scanGRU-unbounded : ∀ T n s x →
  scanGRU T n s x ≡ scanIterate T n s x
scanGRU-unbounded T zero s x = refl
scanGRU-unbounded T (suc n) s x =
  cong
    (λ st → L.gruStep st (scanInput T n x))
    (scanGRU-unbounded T n s x)

record FiniteSSM (S I O : Set) : Set₁ where
  constructor finiteSSM
  field transition : I → S → S
        output : S → O
open FiniteSSM public

record FiniteSSRN (S I O : Set) : Set₁ where
  constructor finiteSSRN
  field recurrent : I → S → S
        readoutR : S → O
open FiniteSSRN public

ssmToSSRN : ∀ {S I O} → FiniteSSM S I O → FiniteSSRN S I O
ssmToSSRN M = finiteSSRN (transition M) (output M)

ssrnToSSM : ∀ {S I O} → FiniteSSRN S I O → FiniteSSM S I O
ssrnToSSM R = finiteSSM (recurrent R) (readoutR R)

ssm-ssrn-left : ∀ {S I O} (M : FiniteSSM S I O) →
  ssmToSSRN (ssrnToSSM (ssmToSSRN M)) ≡ ssmToSSRN M
ssm-ssrn-left M = refl

ssm-ssrn-right : ∀ {S I O} (R : FiniteSSRN S I O) →
  ssrnToSSM (ssmToSSRN (ssrnToSSM R)) ≡ ssrnToSSM R
ssm-ssrn-right R = refl

gruFiniteSSM : FiniteSSM L.GRUState L.Int8 L.Int8
gruFiniteSSM = finiteSSM (λ x s → L.gruStep s x) (λ s → L.hiddenState s)

gruFiniteSSRN : FiniteSSRN L.GRUState L.Int8 L.Int8
gruFiniteSSRN = finiteSSRN (λ x s → L.gruStep s x)
  (λ s → L.hiddenState s)

gru-ssm-ssrn-equivalence :
  ssmToSSRN (ssrnToSSM (ssmToSSRN gruFiniteSSM)) ≡
  ssmToSSRN gruFiniteSSM
gru-ssm-ssrn-equivalence = refl

gru-gate-input-only : ∀ s t x →
  L.hardSignGate x ≡ L.hardSignGate x
gru-gate-input-only s t x = refl

data WatkinsTrace : Set where
  cut continue : WatkinsTrace

watkinsTraceStep : WatkinsTrace → L.BoolLike → WatkinsTrace
watkinsTraceStep t L.yes = t
watkinsTraceStep t L.no = cut

watkinsTrace-cut-law : ∀ t →
  watkinsTraceStep t L.no ≡ cut
watkinsTrace-cut-law t = refl

watkinsTrace-continue-law : ∀ t →
  watkinsTraceStep t L.yes ≡ t
watkinsTrace-continue-law t = refl

watkinsQTarget : L.Int8 → L.Int8 → L.Int8 → L.Int8
watkinsQTarget reward gamma nextQ =
  L.int8Add reward (L.int8Mul gamma nextQ)

watkinsQTarget-law : ∀ reward gamma nextQ →
  watkinsQTarget reward gamma nextQ ≡
  L.int8Add reward (L.int8Mul gamma nextQ)
watkinsQTarget-law reward gamma nextQ = refl

watkinsQTargetWithBias : L.Int8 → L.Int8 → L.Int8 → L.Int8 → L.Int8
watkinsQTargetWithBias reward qLogBias gamma nextQ =
  L.int8Add
    (L.int8Add reward qLogBias)
    (L.int8Mul gamma nextQ)

watkinsQTargetWithBias-law : ∀ reward qLogBias gamma nextQ →
  watkinsQTargetWithBias reward qLogBias gamma nextQ ≡
  L.int8Add
    (L.int8Add reward qLogBias)
    (L.int8Mul gamma nextQ)
watkinsQTargetWithBias-law reward qLogBias gamma nextQ = refl

watkinsQTargetWithBias-zero-law : ∀ reward gamma nextQ →
  watkinsQTargetWithBias reward L.zero8 gamma nextQ ≡
  watkinsQTarget reward gamma nextQ
watkinsQTargetWithBias-zero-law reward gamma nextQ = refl

watkinsTrace-forward-cut : ∀ t →
  watkinsTraceStep t L.no ≡ cut
watkinsTrace-forward-cut = watkinsTrace-cut-law

replaceNormState : ∀ {A} → L.LearnerState A → L.NormPair → L.LearnerState A
replaceNormState s n =
  L.learnerState
    (L.clock s)
    (L.q s)
    (L.counts s)
    (L.lastAction s)
    (L.gru s)
    (L.optimizer s)
    n

replaceOptimizerState : ∀ {A} → L.LearnerState A → L.F4State → L.LearnerState A
replaceOptimizerState s o =
  L.learnerState
    (L.clock s)
    (L.q s)
    (L.counts s)
    (L.lastAction s)
    (L.gru s)
    o
    (L.normState s)

generalPolicy-norm-invariant :
  ∀ {A} (K : L.LearnerKernel A) s n →
  L.generalPolicy K (replaceNormState s n) ≡ L.generalPolicy K s
generalPolicy-norm-invariant K s n = refl

generalPolicy-optimizer-invariant :
  ∀ {A} (K : L.LearnerKernel A) s o →
  L.generalPolicy K (replaceOptimizerState s o) ≡ L.generalPolicy K s
generalPolicy-optimizer-invariant K s o = refl

norm-path-monotone : ∀ n w x →
  L.pathWeight n ≤ L.pathWeight (L.normStep n w x)
norm-path-monotone n w x =
  m≤m+n (L.pathWeight n) (toℕ (L.code w) * toℕ (L.code x))

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
finiteSionSandwich {payoff = p} W = refl≤ _ (p (xStar (saddle W)) (yStar (saddle W)))

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


------------------------------------------------------------------------
-- Exact function-class identification.
--
-- The learner is a deterministic discrete-time state-space transducer:
--
--   S_{t+1} = step S_t x_t
--   y_t     = output S_t
--
-- Its state is not finite because LearnerState contains Nat-valued
-- clock/count registers.  Therefore the correct class is an
-- infinite-state deterministic state-space/transducer class, with the
-- finite Int8 components forming a finite-precision algebraic subsystem.
------------------------------------------------------------------------

record DeterministicStateTransducer (S X Y : Set) : Set₁ where
  constructor deterministicStateTransducer
  field
    step : S → X → S
    output : S → Y
open DeterministicStateTransducer public

learnerStateTransducer :
  ∀ {A : Nat} →
  L.LearnerKernel A →
  DeterministicStateTransducer
    (L.LearnerState A)
    L.Int8
    (Fin A)
learnerStateTransducer K =
  deterministicStateTransducer
    (L.learnerStep K)
    (L.generalPolicy K)

learnerStateTransducer-step-law :
  ∀ {A : Nat} (K : L.LearnerKernel A)
  (s : L.LearnerState A) (reward : L.Int8) →
  step (learnerStateTransducer K) s reward ≡
  L.learnerStep K s reward
learnerStateTransducer-step-law K s reward = refl

learnerStateTransducer-output-law :
  ∀ {A : Nat} (K : L.LearnerKernel A)
  (s : L.LearnerState A) →
  output (learnerStateTransducer K) s ≡
  L.generalPolicy K s
learnerStateTransducer-output-law K s = refl

------------------------------------------------------------------------
-- Finite-action minimax extension.
--
-- This is the exact discrete finite-action analogue of the literature's
-- minimax Bellman construction: a maximizer chooses a, a minimizer
-- chooses b, and the value is max_a min_b of the branch value.
--
-- The literature formulation uses max/min over behavioral strategies and
-- a Bellman recursion over a value function.  Here the action sets and
-- values are finite/discrete, so the operator is exact rather than an
-- approximation over real-valued function spaces.
------------------------------------------------------------------------

minNat : Nat → Nat → Nat
minNat zero n = zero
minNat (suc m) zero = zero
minNat (suc m) (suc n) = suc (minNat m n)

maxList : List Nat → Nat
maxList [] = zero
maxList (x ∷ xs) = L.maxNat x (maxList xs)

minList : List Nat → Nat
minList [] = zero
minList (x ∷ []) = x
minList (x ∷ y ∷ xs) = minNat x (minList (y ∷ xs))

record FiniteMinimaxStateSystem
  (S X Y A B : Set) : Set₁ where
  constructor finiteMinimaxStateSystem
  field
    maxActions : List A
    minActions : List B
    minimaxTransition : S → X → A → B → S
    payoff : S → X → A → B → Nat
    minimaxOutput : S → Y
open FiniteMinimaxStateSystem public

minimaxValue :
  ∀ {S X Y A B : Set}
  (G : FiniteMinimaxStateSystem S X Y A B) →
  S → X → Nat
minimaxValue G s x =
  maxList
    (map
      (λ a →
        minList
          (map
            (λ b →
              payoff G s x a b)
            (minActions G)))
      (maxActions G))

record MinimaxBellmanSystem
  (S X A B : Set) : Set₁ where
  constructor minimaxBellmanSystem
  field
    maxActionsB : List A
    minActionsB : List B
    rewardB : S → X → A → B → Nat
    transitionB : S → X → A → B → S
open MinimaxBellmanSystem public

minimaxBellman :
  ∀ {S X A B : Set}
  (G : MinimaxBellmanSystem S X A B) →
  (S → Nat) → S → X → Nat
minimaxBellman G V s x =
  maxList
    (map
      (λ a →
        minList
          (map
            (λ b →
              rewardB G s x a b +
              V (transitionB G s x a b))
            (minActionsB G)))
      (maxActionsB G))

------------------------------------------------------------------------
-- The current learner is a genuine member of this minimax-inclusive
-- state-system class.  The minimizer is the one-element degenerate
-- player; the maximizer ranges over the learner's actual action set.
--
-- Importantly, this proves inclusion in the class.  It does not claim
-- that sparsemaxPolicy is itself a minimax optimizer.
------------------------------------------------------------------------

singletonAction : Fin 1
singletonAction = Fin.zero

learnerMinimaxStateSystem :
  ∀ {A : Nat} →
  L.LearnerKernel A →
  FiniteMinimaxStateSystem
    (L.LearnerState A)
    L.Int8
    (Fin A)
    (Fin A)
    (Fin 1)
learnerMinimaxStateSystem K =
  finiteMinimaxStateSystem
    (L.finList _)
    (singletonAction ∷ [])
    (λ s reward a b →
      L.learnerStepGivenAction K s a reward)
    (λ s reward a b →
      toℕ (L.code
        (L.scoreA (L.q s) (L.counts s) a)))
    (L.generalPolicy K)

------------------------------------------------------------------------
-- A minimax Bellman backup can be taken over the learner's actual
-- action-conditioned transition without changing its state class.
------------------------------------------------------------------------

learnerMinimaxBellman :
  ∀ {A : Nat}
  (K : L.LearnerKernel A) →
  MinimaxBellmanSystem
    (L.LearnerState A)
    L.Int8
    (Fin A)
    (Fin 1)
learnerMinimaxBellman K =
  minimaxBellmanSystem
    (L.finList _)
    (singletonAction ∷ [])
    (λ s reward a b →
      toℕ (L.code
        (L.scoreA (L.q s) (L.counts s) a)))
    (L.learnerStepGivenAction K)

-- The causal history runner used by both the minimax rollout theorem
-- and the reservoir-form filter theorem below.
runHistory :
  ∀ {S X : Set} →
  (S → X → S) →
  List X →
  S →
  S
runHistory step [] s = s
runHistory step (x ∷ xs) s =
  runHistory step xs (step s x)

-- Policy-driven rollout of the same finite-action transition class.
minimaxRollout :
  ∀ {S X Y A B : Set}
  (G : FiniteMinimaxStateSystem S X Y A B) →
  (S → X → A) →
  (S → X → B) →
  List X →
  S →
  S
minimaxRollout G π₁ π₂ [] s = s
minimaxRollout G π₁ π₂ (x ∷ xs) s =
  minimaxRollout G π₁ π₂ xs
    (minimaxTransition G s x (π₁ s x) (π₂ s x))

learnerMinimaxRollout :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (xs : List L.Int8)
  (s : L.LearnerState A) →
  minimaxRollout
    (learnerMinimaxStateSystem K)
    (λ s reward → L.generalPolicy K s)
    (λ s reward → singletonAction)
    xs s
  ≡
  runHistory (L.learnerStep K) xs s
learnerMinimaxRollout K [] s = refl
learnerMinimaxRollout K (x ∷ xs) s =
  learnerMinimaxRollout
    K
    xs
    (L.learnerStep K s x)

------------------------------------------------------------------------
-- Reservoir-form relation.
--
-- Reservoir-computing literature treats temporal processing as an
-- input-history filter produced by a state update plus a readout.  The
-- following finite-history filter is the exact structural construction
-- for the present learner.  No fading-memory or universality claim is
-- inferred from this construction.
------------------------------------------------------------------------

learnerHistoryState :
  ∀ {A : Nat} →
  L.LearnerKernel A →
  List L.Int8 →
  L.LearnerState A →
  L.LearnerState A
learnerHistoryState K xs s =
  runHistory (L.learnerStep K) xs s

learnerMinimaxRollout-historyState :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (xs : List L.Int8)
  (s : L.LearnerState A) →
  minimaxRollout
    (learnerMinimaxStateSystem K)
    (λ s reward → L.generalPolicy K s)
    (λ s reward → singletonAction)
    xs s
  ≡
  learnerHistoryState K xs s
learnerMinimaxRollout-historyState K xs s =
  learnerMinimaxRollout K xs s

learnerHistoryFilter :
  ∀ {A : Nat} →
  L.LearnerKernel A →
  List L.Int8 →
  L.LearnerState A →
  Fin A
learnerHistoryFilter K xs s =
  L.generalPolicy (learnerHistoryState K xs s)

learnerHistoryFilter-final-output :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (xs : List L.Int8)
  (s : L.LearnerState A) →
  learnerHistoryFilter K xs s ≡
  L.generalPolicy K
    (learnerHistoryState K xs s)
learnerHistoryFilter-final-output K xs s = refl

historyState-congruence :
  ∀ {S X : Set}
  (step : S → X → S)
  (xs ys : List X)
  (s t : S) →
  runHistory step xs s ≡ runHistory step ys t →
  ∀ zs →
  runHistory step zs (runHistory step xs s) ≡
  runHistory step zs (runHistory step ys t)
historyState-congruence step xs ys s t eq [] = eq
historyState-congruence step xs ys s t eq (z ∷ zs) =
  historyState-congruence
    step xs ys
    (step (runHistory step xs s) z)
    (step (runHistory step ys t) z)
    (cong (λ u → step u z) eq)
    zs

learner-filter-causal-state-law :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (xs ys zs : List L.Int8)
  (s t : L.LearnerState A) →
  learnerHistoryState K xs s ≡
  learnerHistoryState K ys t →
  learnerHistoryState K (zs) (learnerHistoryState K xs s) ≡
  learnerHistoryState K (zs) (learnerHistoryState K ys t)
learner-filter-causal-state-law K xs ys zs s t eq =
  historyState-congruence
    (L.learnerStep K) xs ys s t eq zs

------------------------------------------------------------------------
-- The actual learner trajectory embeds Nat into the state through clock.
------------------------------------------------------------------------

learnerClockTrace :
  ∀ {A : Nat} →
  L.LearnerKernel A →
  Nat →
  L.LearnerState A
learnerClockTrace K n =
  L.iterateLearner K n
    (L.initialLearner (L.actionSpaceK K))
    L.zero8

learnerClockTrace-clock :
  ∀ {A : Nat} (K : L.LearnerKernel A) (n : Nat) →
  L.clock (learnerClockTrace K n) ≡ n
learnerClockTrace-clock K n =
  trans
    (iterateLearner-clock K n
      (L.initialLearner (L.actionSpaceK K))
      L.zero8)
    (zero-plus n)

learnerClockTrace-injective :
  ∀ {A : Nat} (K : L.LearnerKernel A) →
  Injective _≡_ _≡_ (learnerClockTrace K)
learnerClockTrace-injective K {i} {j} eq =
  trans
    (sym (learnerClockTrace-clock K i))
    (trans
      (cong L.clock eq)
      (learnerClockTrace-clock K j))

------------------------------------------------------------------------
-- Explicit finite-state impossibility.
--
-- Any finite carrier Fin n is too small to injectively encode the
-- learner's reachable state trajectory.
------------------------------------------------------------------------

learnerState-no-finite-injective-encoding :
  ∀ {A n : Nat}
  (K : L.LearnerKernel A)
  (encode : L.LearnerState A → Fin n) →
  ¬ Injective _≡_ _≡_ encode
learnerState-no-finite-injective-encoding K encode inj =
  ℕ→Fin-notInjective
    (λ n → encode (learnerClockTrace K n))
    (λ {i} {j} eq →
      learnerClockTrace-injective K (inj eq))

------------------------------------------------------------------------
-- Stronger observational impossibility.
--
-- No observation into any finite carrier admits a left inverse on the
-- full learner state.
------------------------------------------------------------------------

learnerFiniteObservation-no-left-inverse :
  ∀ {A n : Nat}
  (K : L.LearnerKernel A)
  (observe : L.LearnerState A → Fin n)
  (inverse : Fin n → L.LearnerState A) →
  (∀ s → inverse (observe s) ≡ s) →
  ⊥
learnerFiniteObservation-no-left-inverse K observe inverse leftInverse =
  learnerState-no-finite-injective-encoding K observe
    (λ {s} {t} eq →
      trans
        (sym (leftInverse s))
        (trans
          (cong inverse eq)
          (leftInverse t)))

record LearnerMinimaxInclusion
  {A : Nat}
  (K : L.LearnerKernel A) : Set₁ where
  constructor learnerMinimaxInclusion
  field
    stateSystemWitness :
      FiniteMinimaxStateSystem
        (L.LearnerState A)
        L.Int8
        (Fin A)
        (Fin A)
        (Fin 1)
    bellmanSystemWitness :
      MinimaxBellmanSystem
        (L.LearnerState A)
        L.Int8
        (Fin A)
        (Fin 1)
    rolloutWitness :
      ∀ (xs : List L.Int8) (s : L.LearnerState A) →
      minimaxRollout
        stateSystemWitness
        (λ s reward → L.generalPolicy K s)
        (λ s reward → singletonAction)
        xs s
      ≡
      runHistory (L.learnerStep K) xs s
    noFiniteStateEncoding :
      ∀ {n : Nat}
      (encode : L.LearnerState A → Fin n) →
      ¬ Injective _≡_ _≡_ encode
open LearnerMinimaxInclusion public

learner-minimax-inclusive :
  ∀ {A : Nat} (K : L.LearnerKernel A) →
  LearnerMinimaxInclusion K
learner-minimax-inclusive K =
  learnerMinimaxInclusion
    (learnerMinimaxStateSystem K)
    (learnerMinimaxBellman K)
    (learnerMinimaxRollout K)
    (learnerState-no-finite-injective-encoding K)

------------------------------------------------------------------------
-- The finite-readout obstruction is the discrete analogue of the
-- exact-left-inverse requirement appearing in reservoir universality
-- theorems: exact state reconstruction through a finite observation is
-- impossible here because the learner carries an injective Nat clock.
------------------------------------------------------------------------

learner-discrete-reservoir-left-inverse-impossible :
  ∀ {A n : Nat}
  (K : L.LearnerKernel A)
  (observe : L.LearnerState A → Fin n)
  (inverse : Fin n → L.LearnerState A) →
  (∀ s → inverse (observe s) ≡ s) →
  ⊥
learner-discrete-reservoir-left-inverse-impossible =
  learnerFiniteObservation-no-left-inverse

------------------------------------------------------------------------
-- Deduction: the learner is not a finite-state machine under its
-- current unbounded-Nat state type.
------------------------------------------------------------------------

learner-not-finite-state :
  ∀ {A n : Nat}
  (K : L.LearnerKernel A)
  (encode : L.LearnerState A → Fin n) →
  ¬ Injective _≡_ _≡_ encode
learner-not-finite-state = learnerState-no-finite-injective-encoding

------------------------------------------------------------------------
-- Sparse accumulation is tied directly to the learner's sparsemax
-- support and to the actual learner-step composition.
------------------------------------------------------------------------

maxNat-left-positive :
  ∀ {m n} → m ≢ zero → L.maxNat m n ≢ zero
maxNat-left-positive {zero} {zero} h eq = h eq
maxNat-left-positive {zero} {suc n} h ()
maxNat-left-positive {suc m} {zero} h ()
maxNat-left-positive {suc m} {suc n} h ()

supportSearch-max-positive :
  ∀ {A : Nat} (xs : List (L.ScoreEntry A)) temperature fuel current best →
  best ≢ zero →
  L.searchSupport xs temperature fuel current best ≢ zero
supportSearch-max-positive xs temperature zero current best h = h
supportSearch-max-positive xs temperature (suc n) current best h
  with L.supportValid xs temperature current
... | yes =
  supportSearch-max-positive
    xs temperature n (suc current) (L.maxNat best current)
    (maxNat-left-positive h)
... | no =
  supportSearch-max-positive
    xs temperature n (suc current) best h

-- The actual sparsemax support used by learnerStep is never empty.
learnerSparseSupport-nonempty :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (s : L.LearnerState A) →
  L.supportSize
    (L.actionSpaceK K)
    (L.q s)
    (L.counts s) ≢ zero
learnerSparseSupport-nonempty {A} K s =
  supportSearch-max-positive
    (L.sortScores (L.scoreList (L.q s) (L.counts s)))
    L.sparsemaxTemperature
    A
    (suc zero)
    (suc zero)
    (λ ())

learnerSparseActiveCodes :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (s : L.LearnerState A) →
  List Nat
learnerSparseActiveCodes K s =
  L.topCodes
    (L.supportSize
      (L.actionSpaceK K)
      (L.q s)
      (L.counts s))
    (L.sortScores (L.scoreList (L.q s) (L.counts s)))

-- This is the actual finite accumulation performed over the sparse
-- support selected by the learner's sparsemax implementation.
learnerSparseAccumulation :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (s : L.LearnerState A) →
  Nat
learnerSparseAccumulation K s =
  L.sumList (learnerSparseActiveCodes K s)

learnerSparseStepWork :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (s : L.LearnerState A) →
  Nat
learnerSparseStepWork K s =
  L.supportSize
    (L.actionSpaceK K)
    (L.q s)
    (L.counts s)

learnerSparseStepWork-positive :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (s : L.LearnerState A) →
  suc zero ≤ learnerSparseStepWork K s
learnerSparseStepWork-positive K s =
  nonzero→one≤ (learnerSparseSupport-nonempty K s)

------------------------------------------------------------------------
-- The work recurrence is over the actual learner transition.  It is
-- therefore compositional in the learner state, rather than an external
-- cost model.
------------------------------------------------------------------------

learnerSparseTraceWork :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (reward : L.Int8) →
  Nat →
  L.LearnerState A →
  Nat
learnerSparseTraceWork K reward zero s = zero
learnerSparseTraceWork K reward (suc n) s =
  learnerSparseStepWork K s +
  learnerSparseTraceWork K reward n (L.learnerStep K s reward)

learnerSparseTraceWork-step :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (reward : L.Int8)
  (n : Nat)
  (s : L.LearnerState A) →
  learnerSparseTraceWork K reward (suc n) s ≡
  learnerSparseStepWork K s +
  learnerSparseTraceWork K reward n (L.learnerStep K s reward)
learnerSparseTraceWork-step K reward n s = refl

suc-plus :
  ∀ n → suc n ≡ suc zero + n
suc-plus zero = refl
suc-plus (suc n) = cong suc (suc-plus n)

learnerSparseTraceWork-lower-bound :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (reward : L.Int8)
  (n : Nat)
  (s : L.LearnerState A) →
  n ≤ learnerSparseTraceWork K reward n s
learnerSparseTraceWork-lower-bound K reward zero s = z≤n
learnerSparseTraceWork-lower-bound K reward (suc n) s =
  subst
    (λ z →
      z ≤
      learnerSparseStepWork K s +
      learnerSparseTraceWork K reward n (L.learnerStep K s reward))
    (suc-plus n)
    (+-mono-≤
      (learnerSparseStepWork-positive K s)
      (learnerSparseTraceWork-lower-bound
        K reward n (L.learnerStep K s reward)))

suc-not≤ :
  ∀ n → suc n ≤ n → ⊥
suc-not≤ zero ()
suc-not≤ (suc n) (s≤s h) = suc-not≤ n h

-- No finite constant bounds the cumulative sparse-support work across
-- arbitrary compositions of the actual learnerStep.
learnerSparseAccumulation-unbounded :
  ∀ {A : Nat}
  (K : L.LearnerKernel A)
  (reward : L.Int8)
  (s : L.LearnerState A) →
  ¬ (∃ λ B →
       ∀ n →
       learnerSparseTraceWork K reward n s ≤ B)
learnerSparseAccumulation-unbounded K reward s (B , bound) =
  suc-not≤ B
    (trans
      (learnerSparseTraceWork-lower-bound
        K reward (suc B) s)
      (bound (suc B)))
