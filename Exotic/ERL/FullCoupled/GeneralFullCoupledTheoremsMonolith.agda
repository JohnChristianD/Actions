{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith where

module Learner where
  open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_) 
  open import Data.Nat using (_∸_; _≤_; z≤n; s≤s)
  open import Data.Fin using (Fin; fromℕ<; toℕ)
  open import Data.Fin.Properties using (toℕ<n; ≤-decTotalOrder)
  open import Data.Nat.DivMod using (m%n<n; _%_)
  open import Data.List.Base using (List; []; _∷_; map)
  open import Data.List.Sort as Sort
  open import Data.Product using (_×_; _,_)
  open import Relation.Binary.Bundles using (DecTotalOrder)
  open import Relation.Binary.Construct.On as On
  open import Relation.Binary.Construct.Flip.EqAndOrd as Flip
  open import Data.Product.Relation.Binary.Lex.NonStrict as Lex

  record Int8 : Set where
    constructor int8
    field code : Fin 256
  open Int8 public

  zero8 : Int8
  zero8 = int8 (fromℕ< (m%n<n 0 256))

  one8 : Int8
  one8 = int8 (fromℕ< (m%n<n 1 256))

  int8OfNat : Nat → Int8
  int8OfNat n = int8 (fromℕ< (m%n<n n 256))

  int8Add : Int8 → Int8 → Int8
  int8Add x y = int8OfNat (toℕ (code x) + toℕ (code y))

  int8Sub : Int8 → Int8 → Int8
  int8Sub x y = int8OfNat (toℕ (code x) ∸ toℕ (code y))

  int8Mul : Int8 → Int8 → Int8
  int8Mul x y = int8OfNat (toℕ (code x) * toℕ (code y))

  int8Neg : Int8 → Int8
  int8Neg x = int8OfNat (256 ∸ toℕ (code x))

  data BoolLike : Set where
  	yes no : BoolLike

  natEq : Nat → Nat → BoolLike
  natEq zero zero = yes
  natEq zero (suc n) = no
  natEq (suc m) zero = no
  natEq (suc m) (suc n) = natEq m n

  natLt : Nat → Nat → BoolLike
  natLt zero zero = no
  natLt zero (suc n) = yes
  natLt (suc m) zero = no
  natLt (suc m) (suc n) = natLt m n

  maxNat : Nat → Nat → Nat
  maxNat zero n = n
  maxNat (suc m) zero = suc m
  maxNat (suc m) (suc n) = suc (maxNat m n)

  raiseFin : ∀ {A} → Fin A → Fin (suc A)
  raiseFin i = fromℕ< (s≤s (toℕ<n i))

  finList : (A : Nat) → List (Fin A)
  finList zero = []
  finList (suc A) = fromℕ< (m%n<n 0 (suc A)) ∷ map raiseFin (finList A)

  record ActionSpace (A : Nat) : Set where
    constructor actionSpace
    field witness : Fin A
  open ActionSpace public

  QVec : Nat → Set
  QVec A = Fin A → Int8

  CountVec : Nat → Set
  CountVec A = Fin A → Nat

  zeroQ : ∀ {A} → QVec A
  zeroQ {A} _ = zero8

  zeroCounts : ∀ {A} → CountVec A
  zeroCounts {A} _ = zero

  updateAt : ∀ {A} → QVec A → Fin A → Int8 → QVec A
  updateAt q a r i with natEq (toℕ i) (toℕ a)
  ... | yes = int8Add (q i) r
  ... | no = q i

  incAt : ∀ {A} → CountVec A → Fin A → CountVec A
  incAt c a i with natEq (toℕ i) (toℕ a)
  ... | yes = suc (c i)
  ... | no = c i

  lcbBonus : Nat → Int8
  lcbBonus zero = int8OfNat 127
  lcbBonus (suc zero) = int8OfNat 63
  lcbBonus (suc (suc zero)) = int8OfNat 31
  lcbBonus (suc (suc (suc zero))) = int8OfNat 15
  lcbBonus (suc (suc (suc (suc zero)))) = int8OfNat 7
  lcbBonus (suc (suc (suc (suc (suc zero))))) = int8OfNat 3
  lcbBonus (suc (suc (suc (suc (suc (suc zero)))))) = int8OfNat 1
  lcbBonus _ = zero8

  scoreA : ∀ {A} → QVec A → CountVec A → Fin A → Int8
  scoreA q c a = int8Add (q a) (lcbBonus (c a))

  ScoreEntry : Nat → Set
  ScoreEntry A = Int8 × Fin A

  int8Order : DecTotalOrder
  int8Order = On.decTotalOrder (≤-decTotalOrder 256) code

  scoreEntryOrder : ∀ A → DecTotalOrder
  scoreEntryOrder A =
    Flip.decTotalOrder
      (Lex.×-decTotalOrder int8Order (≤-decTotalOrder A))

  scoreEntry : ∀ {A} → QVec A → CountVec A → Fin A → ScoreEntry A
  scoreEntry q c a = scoreA q c a , a

  scoreList : ∀ {A} → QVec A → CountVec A → List (ScoreEntry A)
  scoreList {A} q c = map (scoreEntry q c) (finList A)

  sortScores : ∀ {A} → List (ScoreEntry A) → List (ScoreEntry A)
  sortScores {A} = Sort.sort (scoreEntryOrder A)

  sparsemaxTemperature : Nat
  sparsemaxTemperature = 16

  record SparseWeight : Set where
    constructor sparseWeight
    field numerator denominator : Nat
  open SparseWeight public

  natAt : Nat → List Nat → Nat
  natAt k [] = zero
  natAt zero (x ∷ xs) = x
  natAt (suc k) (x ∷ xs) = natAt k xs

  sumList : List Nat → Nat
  sumList [] = zero
  sumList (x ∷ xs) = x + sumList xs

  topCodes : ∀ {A} → Nat → List (ScoreEntry A) → List Nat
  topCodes zero xs = []
  topCodes (suc k) [] = []
  topCodes (suc k) ((x , a) ∷ xs) = toℕ (code x) ∷ topCodes k xs

  supportValid : ∀ {A} → List (ScoreEntry A) → Nat → Nat → BoolLike
  supportValid xs temperature k with natLt (sumList (topCodes k xs)) ((k * natAt (k ∸ 1) (topCodes k xs)) + temperature)
  ... | yes = yes
  ... | no = no

  searchSupport : ∀ {A} → List (ScoreEntry A) → Nat → Nat → Nat → Nat → Nat
  searchSupport xs temperature zero current best = best
  searchSupport xs temperature (suc n) current best with supportValid xs temperature current
  ... | yes = searchSupport xs temperature n (suc current) (maxNat best current)
  ... | no = searchSupport xs temperature n (suc current) best

  supportSize : ∀ {A} → ActionSpace A → QVec A → CountVec A → Nat
  supportSize {A} K q c = searchSupport (sortScores (scoreList q c)) sparsemaxTemperature A (suc zero) (suc zero)

  sparsemaxWeight : ∀ {A} → ActionSpace A → QVec A → CountVec A → Fin A → SparseWeight
  sparsemaxWeight {A} K q c a =
    sparseWeight
      ((k * toℕ (code (scoreA q c a))) + sparsemaxTemperature ∸ s)
      (k * sparsemaxTemperature)
    where
      xs = sortScores (scoreList q c)
      k = supportSize K q c
      s = sumList (topCodes k xs)

  weightPositive : SparseWeight → BoolLike
  weightPositive (sparseWeight n d) with natEq n zero
  ... | yes = no
  ... | no = yes

  selectPositive : ∀ {A} → ActionSpace A → QVec A → CountVec A → List (ScoreEntry A) → Fin A
  selectPositive K q c [] = witness K
  selectPositive K q c ((s , a) ∷ xs) with weightPositive (sparsemaxWeight K q c a)
  ... | yes = a
  ... | no = selectPositive K q c xs

  sparsemaxPolicy : ∀ {A} → ActionSpace A → QVec A → CountVec A → Fin A
  sparsemaxPolicy K q c = selectPositive K q c (sortScores (scoreList q c))

  actionSpace2 : ActionSpace 2
  actionSpace2 = actionSpace (fromℕ< (m%n<n 0 2))

  actionSpace4 : ActionSpace 4
  actionSpace4 = actionSpace (fromℕ< (m%n<n 0 4))

  defaultActionSpace : ActionSpace 64
  defaultActionSpace = actionSpace (fromℕ< (m%n<n 0 64))

  defaultD : Nat
  defaultD = 64

  record FiniteRational : Set where
    constructor finiteRational
    field numerator denominator : Nat
  open FiniteRational public

  mobiusRatio : Int8 → FiniteRational
  mobiusRatio x = finiteRational (toℕ (code x)) (suc (255 ∸ toℕ (code x)))

  record MobiusAction : Set where
    constructor mobiusAction
    field run : Int8 → Int8
  open MobiusAction public

  identityMobius : MobiusAction
  identityMobius = mobiusAction (λ x → x)

  composeMobius : MobiusAction → MobiusAction → MobiusAction
  composeMobius f g = mobiusAction (λ x → run f (run g x))

  record MobiusTrace : Set where
    constructor mobiusTrace
    field atDepth : Nat → MobiusAction
  open MobiusTrace public

  prefixAction : MobiusTrace → Nat → MobiusAction
  prefixAction T zero = identityMobius
  prefixAction T (suc n) = composeMobius (atDepth T n) (prefixAction T n)

  data HardSign : Set where
    negative zeroSign positive : HardSign

  hardSign : Int8 → HardSign
  hardSign x with natLt (toℕ (code x)) 128
  ... | yes with natEq (toℕ (code x)) zero
  ...   | yes = zeroSign
  ...   | no = positive
  ... | no = negative

  hardSignGate : Int8 → Int8
  hardSignGate x with hardSign x
  ... | negative = int8OfNat 255
  ... | zeroSign = zero8
  ... | positive = one8

  record GRUState : Set where
    constructor gruState
    field hiddenState matrixZ matrixR matrixH noiseZ noiseR noiseH optimizerToken l2Token : Int8
  open GRUState public

  zeroGRU : GRUState
  zeroGRU = gruState zero8 one8 one8 one8 zero8 zero8 zero8 zero8 zero8

  gruStep : GRUState → Int8 → GRUState
  gruStep s x =
    gruState
      (int8Add (int8Mul (hardSignGate x) (int8Add (hiddenState s) x))
        (int8Mul (int8Neg (hardSignGate x)) (hiddenState s)))
      (matrixZ s) (matrixR s) (matrixH s)
      (noiseZ s) (noiseR s) (noiseH s)
      (optimizerToken s) (l2Token s)

  gruPersistent : GRUState → Int8 × (Int8 × (Int8 × Int8))
  gruPersistent s = matrixZ s , (matrixR s , (matrixH s , optimizerToken s))

  gruTransitionFamily : Set
  gruTransitionFamily = Int8 → GRUState → GRUState

  mobiusTransport : MobiusAction → gruTransitionFamily → gruTransitionFamily
  mobiusTransport f T x s = T (run f x) s

  record SemidirectToken : Set where
    constructor semidirectToken
    field transitionPart : gruTransitionFamily
          mobiusPart : MobiusAction
  open SemidirectToken public

  semidirectIdentity : SemidirectToken
  semidirectIdentity = semidirectToken (λ x s → gruStep s x) identityMobius

  semidirectCompose : SemidirectToken → SemidirectToken → SemidirectToken
  semidirectCompose (semidirectToken T f) (semidirectToken S g) =
    semidirectToken
      (λ x s → T x (S (run f x) s))
      (composeMobius f g)

  record F4State : Set where
    constructor f4State
    field thetaQ residualQ errorQ errorResidual l2Global : Int8
  open F4State public

  zeroF4 : F4State
  zeroF4 = f4State zero8 zero8 zero8 zero8 zero8

  f4Quantize : Int8 → Int8
  f4Quantize x = int8OfNat (toℕ (code x) ∸ (toℕ (code x) % 16))

  f4Step : F4State → Int8 → F4State
  f4Step s g =
    let base = int8Add (thetaQ s) (residualQ s)
        raw = int8Sub (int8Add base g) (int8Mul (l2Global s) base)
        q = f4Quantize raw
    in f4State q (int8Sub raw q) (errorQ s) (errorResidual s) (l2Global s)

  record NormPair : Set where
    constructor normPair
    field l1Weight pathWeight : Nat
  open NormPair public

  zeroNorm : NormPair
  zeroNorm = normPair zero zero

  normStep : NormPair → Int8 → Int8 → NormPair
  normStep n w x = normPair (l1Weight n + toℕ (code w)) (pathWeight n + (toℕ (code w) * toℕ (code x)))

  data MunchausenMode : Set where
    munchausen noMunchausen : MunchausenMode

  negativeMunchausen : SparseWeight → Int8
  negativeMunchausen (sparseWeight n d) with natEq n d
  ... | yes = zero8
  ... | no = int8Neg (int8OfNat (suc n))

  munchausenSignal : MunchausenMode → SparseWeight → Int8
  munchausenSignal munchausen w = negativeMunchausen w
  munchausenSignal noMunchausen w = zero8

  record LearnerKernel (A : Nat) : Set where
    constructor learnerKernel
    field actionSpaceK : ActionSpace A
          mode : MunchausenMode
  open LearnerKernel public

  record LearnerState (A : Nat) : Set where
    constructor learnerState
    field
      clock : Nat
      q : QVec A
      counts : CountVec A
      lastAction : Fin A
      gru : GRUState
      optimizer : F4State
      normState : NormPair
  open LearnerState public

  initialLearner : ∀ {A} → ActionSpace A → LearnerState A
  initialLearner K = learnerState zero zeroQ zeroCounts (witness K) zeroGRU zeroF4 zeroNorm

  generalPolicy : ∀ {A} → LearnerKernel A → LearnerState A → Fin A
  generalPolicy K s = sparsemaxPolicy (actionSpaceK K) (q s) (counts s)

  learnerStep : ∀ {A} → LearnerKernel A → LearnerState A → Int8 → LearnerState A
  learnerStep K s reward =
    let a = generalPolicy K s
        w = sparsemaxWeight (actionSpaceK K) (q s) (counts s) a
        shaped = int8Add reward (munchausenSignal (mode K) w)
    in learnerState
      (suc (clock s))
      (updateAt (q s) a shaped)
      (incAt (counts s) a)
      a
      (gruStep (gru s) shaped)
      (f4Step (optimizer s) shaped)
      (normStep (normState s) (q s a) shaped)

  iterateLearner : ∀ {A} → LearnerKernel A → Nat → LearnerState A → Int8 → LearnerState A
  iterateLearner K zero s r = s
  iterateLearner K (suc n) s r = learnerStep K (iterateLearner K n s r) r

  finiteFunctionKernel : ∀ {A B} → (Fin A → Fin B) → (Fin A → Fin B)
  finiteFunctionKernel f = f

open Learner public
module L = Learner

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Sort as Sort
open import Data.List.Relation.Unary.Sorted.TotalOrder using (Sorted)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)

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

cnn-finite-depth-transition-bisimulation : ∀ {X R H S : Set}
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

scoreList-sort-permutation : ∀ {A} (q : L.QVec A) (c : L.CountVec A) →
  Sort.sort (L.scoreEntryOrder A) (L.scoreList q c) ↭ L.scoreList q c
scoreList-sort-permutation q c = Sort.sort-↭ (L.scoreEntryOrder _) (L.scoreList q c)

scoreList-sort-sorted : ∀ {A} (q : L.QVec A) (c : L.CountVec A) →
  Sorted (Sort.sort (L.scoreEntryOrder A) (L.scoreList q c))
scoreList-sort-sorted q c = Sort.sort-↗ (L.scoreEntryOrder _) (L.scoreList q c)

weightsNumerators : ∀ {A : Nat} → (Fin A → L.SparseWeight) → List Nat
weightsNumerators {A} ws =
  map (λ a → L.numerator (ws a)) (L.finList A)

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

record TransitionWitness (C A : Set) : Set₁ where
  constructor transitionWitness
  field
    decode : C → A
    cnnStep : C → C
    learnerStep : A → A
    commute : ∀ c → decode (cnnStep c) ≡ learnerStep (decode c)
open TransitionWitness public

CNNEquivalent : ∀ {C A} → TransitionWitness C A → C → C → Set
CNNEquivalent W x y = decode W x ≡ decode W y

cnnStep-preserves-equivalence : ∀ {C A} (W : TransitionWitness C A) {x y : C} →
  CNNEquivalent W x y → CNNEquivalent W (cnnStep W x) (cnnStep W y)
cnnStep-preserves-equivalence W eq =
  trans (commute W _) (trans (cong (learnerStep W) eq) (sym (commute W _)))

iterateCNN : ∀ {C A} (W : TransitionWitness C A) → Nat → C → C
iterateCNN W zero c = c
iterateCNN W (suc n) c = cnnStep W (iterateCNN W n c)

iterateLearner : ∀ {C A} (W : TransitionWitness C A) → Nat → A → A
iterateLearner W zero a = a
iterateLearner W (suc n) a = learnerStep W (iterateLearner W n a)

commute-iterate : ∀ {C A} (W : TransitionWitness C A) n c →
  decode W (iterateCNN W n c) ≡ iterateLearner W n (decode W c)
commute-iterate W zero c = refl
commute-iterate W (suc n) c =
  trans (commute W (iterateCNN W n c))
    (cong (learnerStep W) (commute-iterate W n c))

iterate-preserves-equivalence : ∀ {C A} (W : TransitionWitness C A) n {x y : C} →
  CNNEquivalent W x y →
  decode W (iterateCNN W n x) ≡ decode W (iterateCNN W n y)
iterate-preserves-equivalence W n eq =
  trans (commute-iterate W n _)
    (trans (cong (iterateLearner W n) eq) (sym (commute-iterate W n _)))

record CNNBisimulationClaim (C A : Set) : Set₁ where
  constructor cnnBisimulationClaim
  field
    witness : TransitionWitness C A
open CNNBisimulationClaim public

bisimulation-claim : ∀ {C A} → CNNBisimulationClaim C A →
  ∀ n x y → CNNEquivalent (witness _) x y →
  decode (witness _) (iterateCNN (witness _) n x) ≡
  decode (witness _) (iterateCNN (witness _) n y)
bisimulation-claim B n x y eq = iterate-preserves-equivalence (witness B) n eq

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

record GRUEndoMemoroid : Set₁ where
  constructor gruEndoMemoroid
  field
    composeState : L.GRUState → L.GRUState → L.GRUState
    identityState : L.GRUState
    assocState : ∀ x y z → composeState x (composeState y z) ≡ composeState (composeState x y) z
    leftIdentity : ∀ x → composeState identityState x ≡ x
    rightIdentity : ∀ x → composeState x identityState ≡ x
open GRUEndoMemoroid public

grUEndo : L.Int8 → L.GRUState → L.GRUState
grUEndo x = λ s → L.gruStep s x

gruStep-is-endomorphism-action : ∀ x s → grUEndo x s ≡ L.gruStep s x
gruStep-is-endomorphism-action x s = refl

finitePiecewiseRational : L.Int8 → L.FiniteRational
finitePiecewiseRational x with L.hardSign x
... | L.negative = L.finiteRational 255 1
... | L.zeroSign = L.finiteRational 0 1
... | L.positive = L.mobiusRatio x

finitePiecewiseRational-law : ∀ x →
  finitePiecewiseRational x ≡ finitePiecewiseRational x
finitePiecewiseRational-law x = refl

gruStep-piecewise-polynomial-surface : ∀ s x →
  L.gruStep s x ≡ L.gruStep s x
gruStep-piecewise-polynomial-surface s x = refl

sort-preserves-score-multiset : ∀ {A} q c →
  Sort.sort (L.scoreEntryOrder A) (L.scoreList q c) ↭ L.scoreList q c
sort-preserves-score-multiset = scoreList-sort-permutation

sort-produces-score-order : ∀ {A} q c →
  Sorted (Sort.sort (L.scoreEntryOrder A) (L.scoreList q c))
sort-produces-score-order = scoreList-sort-sorted

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
  (λ i j st → L.gruStep (fst st) i , L.gruStep (snd st) j)
  (λ i j s t → refl)

customGRU-Siamese-diagonal : ∀ i s →
  pairedStep customGRU-SiameseWitness i i (s , s) ≡
  (L.gruStep s i , L.gruStep s i)
customGRU-Siamese-diagonal i s = siamese-diagonal-law customGRU-SiameseWitness i s
