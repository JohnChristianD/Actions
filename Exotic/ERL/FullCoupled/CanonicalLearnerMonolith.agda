{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (NonZero; _∸_; _<_; _≤_; _<ᵇ_; _/_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-antisym)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n; ≤-decTotalOrder; ℕ→Fin-notInjective)
open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Sort as Sort
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Binary.Construct.On as On
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Data.Product.Relation.Binary.Lex.NonStrict as Lex
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
------------------------------------------------------------------------
-- Minimal topology foundation. Continuity is a concrete property over
-- explicit topologies. Algebraic structure remains topology-independent.
------------------------------------------------------------------------

record Topology (A : Set) : Set₁ where
  field
    isOpen : (A → Set) → Set
    emptyOpen : isOpen (λ _ → ⊥)
    wholeOpen : isOpen (λ _ → ⊤)
    intersectionOpen : ∀ {U V} → isOpen U → isOpen V →
      isOpen (λ x → U x × V x)
    unionOpen : ∀ {I : Set} (U : I → A → Set) →
      (∀ i → isOpen (U i)) →
      isOpen (λ x → Σ I (λ i → U i x))

open Topology public

Continuous : (A B : Set) →
  Topology A → Topology B → (A → B) → Set₁
Continuous A B τA τB f =
  ∀ {V : B → Set} →
  isOpen τB V →
  isOpen τA (λ x → V (f x))

------------------------------------------------------------------------
-- Explicit discrete topology boundary.
--
-- Every predicate is open, so continuity is automatic.  In this finite
-- algebra, therefore, continuity cannot repair a missing global inverse.
------------------------------------------------------------------------

discreteTopology : ∀ (A : Set) → Topology A
discreteTopology A =
  record
    { isOpen = λ _ → ⊤
    ; emptyOpen = tt
    ; wholeOpen = tt
    ; intersectionOpen = λ _ _ → tt
    ; unionOpen = λ _ _ → tt
    }

continuous-under-discrete-topology :
  ∀ {A B : Set} (f : A → B) →
  Continuous A B (discreteTopology A) (discreteTopology B) f
continuous-under-discrete-topology {A} {B} f {V} _ = tt



record Int8 : Set where
  constructor int8
  field code : Fin 256
open Int8 public

int8StateSpace : Set
int8StateSpace = Fin 256

zero8 : Int8
zero8 = int8 (fromℕ< (m%n<n 0 256))

one8 : Int8
one8 = int8 (fromℕ< (m%n<n 1 256))

int8OfNat : Nat → Int8
int8OfNat n = int8 (fromℕ< (m%n<n n 256))

int8Add : Int8 → Int8 → Int8
int8Add x y = int8OfNat (toℕ (code x) + toℕ (code y))

int8Mul : Int8 → Int8 → Int8
int8Mul x y = int8OfNat (toℕ (code x) * toℕ (code y))

int8Neg : Int8 → Int8
int8Neg x = int8OfNat (256 ∸ toℕ (code x))

int8Sub : Int8 → Int8 → Int8
int8Sub x y = int8Add x (int8Neg y)

int8Roundtrip : ∀ x → toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
int8Roundtrip x = trans
  (toℕ-fromℕ< (m%n<n (toℕ (code x)) 256))
  (m<n⇒m%n≡m (toℕ<n (code x)))

le-refl : ∀ n → n ≤ n
le-refl zero = z≤n
le-refl (suc n) = s≤s (le-refl n)

lt-irrefl : ∀ n → (n < n) → ⊥
lt-irrefl zero ()
lt-irrefl (suc n) (s≤s p) = lt-irrefl n p

plus-zero : ∀ n → n + zero ≡ n
plus-zero zero = refl
plus-zero (suc n) = cong suc (plus-zero n)

plus-suc : ∀ (m n : Nat) → m + suc n ≡ suc (m + n)
plus-suc zero n = refl
plus-suc (suc m) n = cong suc (plus-suc m n)

plus-suc-lt : ∀ (m n : Nat) → m < m + suc n
plus-suc-lt zero n = s≤s z≤n
plus-suc-lt (suc m) n = s≤s (plus-suc-lt m n)

plus-suc-not-self : ∀ (m n : Nat) → m + suc n ≢ m
plus-suc-not-self m n eq =
  lt-irrefl m (subst (λ z → m < z) eq (plus-suc-lt m n))

suc-suc-lt : ∀ n → n < suc (suc n)
suc-suc-lt zero = s≤s z≤n
suc-suc-lt (suc n) = s≤s (suc-suc-lt n)

suc-suc-not-self : ∀ n → suc (suc n) ≢ n
suc-suc-not-self n eq =
  lt-irrefl (suc (suc n))
    (subst (λ z → z < suc (suc n)) (sym eq) (suc-suc-lt n))

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate step zero s = s
iterate step (suc n) s = step (iterate step n s)

OrbitNonFixed : ∀ {S : Set} {step : S → S} → S → Set
OrbitNonFixed {step = step} s = ∀ n → iterate step n s ≢ step (iterate step n s)

data Signed : Set where
  neg : Nat → Signed
  zer : Signed
  pos : Nat → Signed

signedCode : Int8 → Signed
signedCode x with toℕ (code x) <ᵇ 128
... | true with toℕ (code x)
...   | zero = zer
...   | suc n = pos (suc n)
... | false with 256 ∸ toℕ (code x)
...   | zero = zer
...   | suc n = neg (suc n)

record FiniteRational : Set where
  constructor finiteRational
  field sign numerator denominator : Nat
open FiniteRational public

data BoolLike : Set where
  enabled disabled : BoolLike

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

natEq : Nat → Nat → BoolLike
natEq zero zero = enabled
natEq zero (suc n) = disabled
natEq (suc m) zero = disabled
natEq (suc m) (suc n) = natEq m n

natLt : Nat → Nat → BoolLike
natLt zero zero = disabled
natLt zero (suc n) = enabled
natLt (suc m) zero = disabled
natLt (suc m) (suc n) = natLt m n

natLE : Nat → Nat → BoolLike
natLE zero n = enabled
natLE (suc m) zero = disabled
natLE (suc m) (suc n) = natLE m n

maxNat : Nat → Nat → Nat
maxNat zero n = n
maxNat (suc m) zero = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

raiseFin : ∀ {A} → Fin A → Fin (suc A)
raiseFin i = fromℕ< (s≤s (toℕ<n i))

finList : (A : Nat) → List (Fin A)
finList zero = []
finList (suc A) = fromℕ< (m%n<n 0 (suc A)) ∷ map raiseFin (finList A)

updateAt : ∀ {A} → QVec A → Fin A → Int8 → QVec A
updateAt q a r i with natEq (toℕ i) (toℕ a)
... | enabled = int8Add (q i) r
... | disabled = q i

incAt : ∀ {A} → CountVec A → Fin A → CountVec A
incAt c a i with natEq (toℕ i) (toℕ a)
... | enabled = suc (c i)
... | disabled = c i

record CriticState (A : Nat) : Set where
  constructor criticState
  field values : QVec A
open CriticState public

record WatkinsKernel (A : Nat) : Set₁ where
  constructor mkWatkinsKernel
  field
    updateCritic : CriticState A → Int8 → CriticState A
    greedy : CriticState A → Int8 → BoolLike
    traceUpdate : BoolLike → BoolLike → BoolLike
open WatkinsKernel public

record WatkinsState (A : Nat) : Set where
  constructor watkinsState
  field critic : CriticState A
        signal : Int8
        trace : BoolLike
open WatkinsState public

watkinsStep : ∀ {A} → WatkinsKernel A → WatkinsState A → WatkinsState A
watkinsStep K s = watkinsState
  (updateCritic K (critic s) (signal s))
  (signal s)
  (traceUpdate K (trace s) (greedy K (critic s) (signal s)))

record LCBCountState (A : Nat) : Set where
  constructor lcbCountState
  field valuesCount : CountVec A
        totalCount : Nat
open LCBCountState public

record LCBCountKernel : Set₁ where
  constructor lcbCountKernel
  field bonus : Nat → Int8
open LCBCountKernel public

finiteLCBBonus8 : Nat → Int8
finiteLCBBonus8 zero = int8OfNat 127
finiteLCBBonus8 (suc zero) = int8OfNat 63
finiteLCBBonus8 (suc (suc zero)) = int8OfNat 31
finiteLCBBonus8 (suc (suc (suc zero))) = int8OfNat 15
finiteLCBBonus8 (suc (suc (suc (suc zero)))) = int8OfNat 7
finiteLCBBonus8 (suc (suc (suc (suc (suc zero))))) = int8OfNat 3
finiteLCBBonus8 (suc (suc (suc (suc (suc (suc zero)))))) = int8OfNat 1
finiteLCBBonus8 _ = zero8

lcbNegate : Int8 → Int8
lcbNegate x = int8OfNat (256 ∸ toℕ (code x))

scoreA : ∀ {A} → QVec A → CountVec A → Fin A → Int8
scoreA q c a = int8Add (q a) (lcbNegate (finiteLCBBonus8 (c a)))

lcbScore : ∀ {A} → LCBCountKernel → LCBCountState A → CriticState A → QVec A
lcbScore L c q a = int8Add (values q a) (lcbNegate (bonus L (valuesCount c a)))

sparsemaxTemperature : Nat
sparsemaxTemperature = 16

ScoreEntry : Nat → Set
ScoreEntry A = Int8 × Fin A

int8Order : DecTotalOrder 0ℓ 0ℓ 0ℓ
int8Order = On.decTotalOrder (≤-decTotalOrder 256) code

scoreEntryOrder : ∀ A → DecTotalOrder 0ℓ 0ℓ 0ℓ
scoreEntryOrder A = Flip.decTotalOrder (Lex.×-decTotalOrder int8Order (≤-decTotalOrder A))

scoreList : ∀ {A} → QVec A → CountVec A → List (ScoreEntry A)
scoreList {A} q c = map (λ a → (scoreA q c a , a)) (finList A)

sortScores : ∀ {A} → List (ScoreEntry A) → List (ScoreEntry A)
sortScores {A} = Sort.sort (scoreEntryOrder A)

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
... | enabled = enabled
... | disabled = disabled

searchSupport : ∀ {A} → List (ScoreEntry A) → Nat → Nat → Nat → Nat → Nat
searchSupport xs temperature zero current best = best
searchSupport xs temperature (suc n) current best with supportValid xs temperature current
... | enabled = searchSupport xs temperature n (suc current) (maxNat best current)
... | disabled = searchSupport xs temperature n (suc current) best

supportSize : ∀ {A} → ActionSpace A → QVec A → CountVec A → Nat
supportSize {A} K q c = searchSupport (sortScores (scoreList q c)) sparsemaxTemperature A (suc zero) (suc zero)

record SparseWeight : Set where
  constructor sparseWeight
  field numerator denominator : Nat
open SparseWeight public

sparsemaxWeight : ∀ {A} → ActionSpace A → QVec A → CountVec A → Fin A → SparseWeight
sparsemaxWeight {A} K q c a = sparseWeight ((k * toℕ (code (scoreA q c a))) + sparsemaxTemperature ∸ s) (k * sparsemaxTemperature)
  where
    xs = sortScores (scoreList q c)
    k = supportSize K q c
    s = sumList (topCodes k xs)

weightPositive : SparseWeight → BoolLike
weightPositive (sparseWeight n d) with natEq n zero
... | enabled = disabled
... | disabled = enabled

selectPositive : ∀ {A} → ActionSpace A → QVec A → CountVec A → List (ScoreEntry A) → Fin A
selectPositive K q c [] = witness K
selectPositive K q c ((s , a) ∷ xs) with weightPositive (sparsemaxWeight K q c a)
... | enabled = a
... | disabled = selectPositive K q c xs

sparsemaxPolicy : ∀ {A} → ActionSpace A → QVec A → CountVec A → Fin A
sparsemaxPolicy {A} K q c = selectPositive K q c (sortScores (scoreList q c))

updateLCBCount : ∀ {A} → Fin A → LCBCountState A → LCBCountState A
updateLCBCount a (lcbCountState counts total) =
  lcbCountState (incAt counts a) (suc total)

finiteQLog8 : Int8 → FiniteRational
finiteQLog8 x with toℕ (code x)
... | zero = finiteRational 1 0 1
... | suc n = finiteRational 1 (128 ∸ suc n) (suc n)

finiteQLog8-denominator-nonZero :
  ∀ {x} → NonZero (denominator (finiteQLog8 x))
finiteQLog8-denominator-nonZero {x} with toℕ (code x)
... | zero = Data.Nat.nonZero
... | suc n = Data.Nat.nonZero

negativeFiniteQLog8 : Int8 → FiniteRational
negativeFiniteQLog8 x = finiteQLog8 x

negativeFiniteQLogLaw :
  ∀ x →
  negativeFiniteQLog8 x ≡
  finiteRational 1
    (numerator (finiteQLog8 x))
    (denominator (finiteQLog8 x))
negativeFiniteQLogLaw x with toℕ (code x)
... | zero = refl
... | suc n = refl

munchausenScale8 : Nat
munchausenScale8 = 16

finiteSignedRationalBias8 : FiniteRational → Int8
finiteSignedRationalBias8 (finiteRational zero n d) = zero8
finiteSignedRationalBias8 (finiteRational (suc s) n zero) = zero8
finiteSignedRationalBias8 (finiteRational (suc s) n (suc d)) =
  int8Neg (int8OfNat ((munchausenScale8 * n) / suc d))

qLog2Bias8 : Int8 → Int8
qLog2Bias8 x =
  finiteSignedRationalBias8 (finiteQLog8 x)

negativeAlpha8 : Int8
negativeAlpha8 = int8OfNat 255

record SignedQLogControl : Set where
  constructor signedQLogControl
  field mode coefficient : Int8
open SignedQLogControl public

canonicalQLogControl : SignedQLogControl
canonicalQLogControl =
  signedQLogControl negativeAlpha8 negativeAlpha8

qLogSignal : SignedQLogControl → Int8 → Int8
qLogSignal c x = int8Add x (coefficient c)

canonicalActionCount : Nat
canonicalActionCount = 64

canonicalActionSpace : ActionSpace canonicalActionCount
canonicalActionSpace = actionSpace (fromℕ< (m%n<n 0 canonicalActionCount))

actionSpace4 : ActionSpace 4
actionSpace4 = actionSpace (fromℕ< (m%n<n 0 4))

defaultActionSpace : ActionSpace 64
defaultActionSpace = canonicalActionSpace

data HardSign : Set where
  negative zeroSign positive : HardSign

hardSignNonnegative : Int8 → HardSign
hardSignNonnegative x with natEq (toℕ (code x)) zero
... | enabled = zeroSign
... | disabled = positive

hardSign : Int8 → HardSign
hardSign x with natLt (toℕ (code x)) 128
... | enabled = hardSignNonnegative x
... | disabled = negative

hardSignGate : Int8 → Int8
hardSignGate x with hardSign x
... | negative = int8OfNat 255
... | zeroSign = zero8
... | positive = one8

record GRUMatrices : Set where
  constructor gruMatrices
  field matrixZ matrixR matrixH : Int8
open GRUMatrices public

record GRUNoise : Set where
  constructor gruNoise
  field noiseZ noiseR noiseH : Int8
open GRUNoise public

record GlobalControl : Set where
  constructor mkGlobalControl
  field optimizerToken l2Token : Int8
open GlobalControl public

record GRUState : Set where
  constructor gruState
  field hiddenState : Int8
        matrixState : GRUMatrices
        noiseState : GRUNoise
        controlState : GlobalControl
open GRUState public

identityGRUMatrices : GRUMatrices
identityGRUMatrices = gruMatrices one8 one8 one8

zeroGRUNoise : GRUNoise
zeroGRUNoise = gruNoise zero8 zero8 zero8

zeroGlobalControl : GlobalControl
zeroGlobalControl = mkGlobalControl zero8 zero8

rationalCode : FiniteRational → Int8
rationalCode (finiteRational s n d) = int8OfNat n

identityActivation8 : Int8 → Int8
identityActivation8 x = x

identityActivation8-law : ∀ x → identityActivation8 x ≡ x
identityActivation8-law x = refl

identityActivation8-zero : identityActivation8 zero8 ≡ zero8
identityActivation8-zero = refl

gruCandidate8 : Int8 → Int8 → Int8
gruCandidate8 h x = int8Add h x

complement128 : Nat → Nat
complement128 n = 128 ∸ n

mix8 : Int8 → Int8 → Int8 → Int8
mix8 g old new = int8Add
  (int8Mul (int8OfNat (complement128 (toℕ (code g)))) old)
  (int8Mul g new)

gateCode : Signed → Int8
gateCode (neg n) = int8OfNat 0
gateCode zer = int8OfNat 64
gateCode (pos n) = int8OfNat 128

gateFromInput : Int8 → Int8
gateFromInput x = gateCode (signedCode x)

gruStep : GRUState → Int8 → GRUState
gruStep (gruState h m n g) x =
  gruState
    (mix8 (gateFromInput x) h
      (int8Add (identityActivation8 x) (gruCandidate8 h x)))
    m n g

persistentGRU : GRUState → GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU (gruState h m n g) = m , (n , g)

persistent-preservation : ∀ (s : GRUState) (x : Int8) →
  persistentGRU (gruStep s x) ≡ persistentGRU s
persistent-preservation (gruState h m n g) x = refl

gruParameterPersistence : ∀ (s : GRUState) (x : Int8) →
  matrixState (gruStep s x) ≡ matrixState s ×
  noiseState (gruStep s x) ≡ noiseState s ×
  controlState (gruStep s x) ≡ controlState s
gruParameterPersistence (gruState h m n g) x = refl , (refl , refl)

GRUEquivalent : GRUState → GRUState → Set
GRUEquivalent s t = persistentGRU s ≡ persistentGRU t

gruEquivalent-refl : ∀ s → GRUEquivalent s s
gruEquivalent-refl s = refl

gruStep-respects-equivalence : ∀ (s t : GRUState) (x : Int8) →
  GRUEquivalent s t → GRUEquivalent (gruStep s x) (gruStep t x)
gruStep-respects-equivalence s t x eq =
  trans (persistent-preservation s x)
    (trans eq (sym (persistent-preservation t x)))

record GRUAction : Set₁ where
  constructor gruAction
  field runGRU : GRUState → GRUState
open GRUAction public

identityGRUAction : GRUAction
identityGRUAction = gruAction (λ s → s)

composeGRUAction : GRUAction → GRUAction → GRUAction
composeGRUAction f g = gruAction (λ s → runGRU f (runGRU g s))

gruActionAssociativity : ∀ f g h s →
  runGRU (composeGRUAction (composeGRUAction f g) h) s ≡
  runGRU (composeGRUAction f (composeGRUAction g h)) s
gruActionAssociativity f g h s = refl

inputGRUAction : Int8 → GRUAction
inputGRUAction x = gruAction (λ s → gruStep s x)

record RecurrentNetwork (State Input : Set) : Set₁ where
  constructor recurrentNetwork
  field
    runNetwork : State → Input → State
open RecurrentNetwork public

canonicalGRURecurrentNetwork : RecurrentNetwork GRUState Int8
canonicalGRURecurrentNetwork =
  recurrentNetwork gruStep

canonicalGRUNetwork-law :
  ∀ (s : GRUState) (x : Int8) →
  runNetwork canonicalGRURecurrentNetwork s x
  ≡
  gruStep s x
canonicalGRUNetwork-law s x = refl

record Endomorphism (State : Set) : Set₁ where
  constructor endomorphism
  field
    applyEndomorphism : State → State
open Endomorphism public

identityEndomorphism : ∀ {State : Set} → Endomorphism State
identityEndomorphism = endomorphism (λ s → s)

composeEndomorphism :
  ∀ {State : Set} →
  Endomorphism State →
  Endomorphism State →
  Endomorphism State
composeEndomorphism f g =
  endomorphism
    (λ s →
      applyEndomorphism f
        (applyEndomorphism g s))

endomorphismAssociative :
  ∀ {State : Set} (f g h : Endomorphism State) s →
  applyEndomorphism
    (composeEndomorphism
      (composeEndomorphism f g)
      h)
    s
  ≡
  applyEndomorphism
    (composeEndomorphism
      f
      (composeEndomorphism g h))
    s
endomorphismAssociative f g h s = refl

recurrentInputEndomorphism :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  Input →
  Endomorphism State
recurrentInputEndomorphism R x =
  endomorphism (λ s → runNetwork R s x)

recurrentPrefixState :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  (Nat → Input) →
  Nat →
  State →
  State
recurrentPrefixState R xs zero s = s
recurrentPrefixState R xs (suc n) s =
  runNetwork R
    (recurrentPrefixState R xs n s)
    (xs n)

recurrentPrefixEndomorphism :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  (Nat → Input) →
  Nat →
  Endomorphism State
recurrentPrefixEndomorphism R xs zero =
  identityEndomorphism
recurrentPrefixEndomorphism R xs (suc n) =
  composeEndomorphism
    (recurrentInputEndomorphism R (xs n))
    (recurrentPrefixEndomorphism R xs n)

recurrentPrefix-correct :
  ∀ {State Input : Set}
  (R : RecurrentNetwork State Input)
  (xs : Nat → Input)
  (n : Nat)
  (s : State) →
  applyEndomorphism
    (recurrentPrefixEndomorphism R xs n)
    s
  ≡
  recurrentPrefixState R xs n s
recurrentPrefix-correct R xs zero s = refl
recurrentPrefix-correct R xs (suc n) s =
  cong
    (λ z → runNetwork R z (xs n))
    (recurrentPrefix-correct R xs n s)

shiftInput :
  ∀ {Input : Set} →
  (Nat → Input) →
  Nat →
  Nat →
  Input
shiftInput xs m n = xs (m + n)

recurrentPrefix-split :
  ∀ {State Input : Set}
  (R : RecurrentNetwork State Input)
  (xs : Nat → Input)
  (m n : Nat)
  (s : State) →
  recurrentPrefixState R xs (m + n) s
  ≡
  recurrentPrefixState
    R
    (shiftInput xs m)
    n
    (recurrentPrefixState R xs m s)
recurrentPrefix-split R xs m zero s rewrite +-identityʳ m = refl
recurrentPrefix-split R xs m (suc n) s rewrite +-suc m n =
  cong
    (λ z → runNetwork R z (xs (m + n)))
    (recurrentPrefix-split R xs m n s)

canonicalGRU-recurrent-prefix-correct :
  ∀ (xs : Nat → Int8) (n : Nat) (s : GRUState) →
  applyEndomorphism
    (recurrentPrefixEndomorphism
      canonicalGRURecurrentNetwork
      xs
      n)
    s
  ≡
  recurrentPrefixState
    canonicalGRURecurrentNetwork
    xs
    n
    s
canonicalGRU-recurrent-prefix-correct =
  recurrentPrefix-correct canonicalGRURecurrentNetwork

canonicalGRU-recurrent-prefix-split :
  ∀ (xs : Nat → Int8) (m n : Nat) (s : GRUState) →
  recurrentPrefixState
    canonicalGRURecurrentNetwork
    xs
    (m + n)
    s
  ≡
  recurrentPrefixState
    canonicalGRURecurrentNetwork
    (shiftInput xs m)
    n
    (recurrentPrefixState
      canonicalGRURecurrentNetwork
      xs
      m
      s)
canonicalGRU-recurrent-prefix-split =
  recurrentPrefix-split canonicalGRURecurrentNetwork

int8-no-countably-unbounded-injective :
  ∀ (f : Nat → Int8) →
  ¬ (∀ {m n} → f m ≡ f n → m ≡ n)
int8-no-countably-unbounded-injective f inj =
  ℕ→Fin-notInjective
    (λ n → code (f n))
    (λ {m} {n} eq → inj (cong int8 eq))

gruInputActionAssociativity : ∀ x y z s →
  runGRU (composeGRUAction (composeGRUAction (inputGRUAction x) (inputGRUAction y)) (inputGRUAction z)) s ≡
  runGRU (composeGRUAction (inputGRUAction x) (composeGRUAction (inputGRUAction y) (inputGRUAction z))) s
gruInputActionAssociativity x y z s = refl

gruStateInt8CoordinateCount : Nat
gruStateInt8CoordinateCount = 9

criticInt8CoordinateCount : Nat
criticInt8CoordinateCount = 2

gruPersistentQuotientCoordinateCount : Nat
gruPersistentQuotientCoordinateCount = 8

fullLearnerInt8CoordinateCount : Nat
fullLearnerInt8CoordinateCount = 23

fullLearnerInt8CoordinateCount-law : fullLearnerInt8CoordinateCount ≡ 23
fullLearnerInt8CoordinateCount-law = refl

record F4IntUState : Set where
  constructor f4IntUState
  field thetaQ rTheta eQ rE rL : Int8
open F4IntUState public

record F4IntUKernel : Set₁ where
  constructor f4IntUKernel
  field globalL2 : Int8
open F4IntUKernel public

f4ThetaFull : F4IntUState → Int8
f4ThetaFull s = thetaQ s

f4ThetaFull-law : ∀ s → f4ThetaFull s ≡ thetaQ s
f4ThetaFull-law s = refl

l2Correction : Int8 → Int8
l2Correction x = lcbNegate x

f4ThetaStep : F4IntUKernel → F4IntUState → Int8 → F4IntUState
f4ThetaStep K s g =
  f4IntUState
    (int8Add (int8Add (thetaQ s) g) (l2Correction (globalL2 K)))
    zero8 (eQ s) (rE s) (rL s)

f4ParameterInvariant : ∀ (K : F4IntUKernel) (s : F4IntUState) (g : Int8) →
  thetaQ (f4ThetaStep K s g) ≡
  int8Add (int8Add (thetaQ s) g) (l2Correction (globalL2 K))
f4ParameterInvariant K s g = refl

record NormPair : Set where
  constructor normPair
  field l1 path : Int8
open NormPair public

normPairWeight : NormPair → Int8
normPairWeight n = int8Add (l1 n) (path n)

normPairWeightPlusOne : NormPair → Int8
normPairWeightPlusOne n = int8Add one8 (normPairWeight n)

record FullLearnerState (A : Nat) : Set₁ where
  constructor fullLearnerState
  field
    clock : Nat
    watkins : WatkinsState A
    gru : GRUState
    optimizer : F4IntUState
    norm : NormPair
    lcbCounts : LCBCountState A
    qLogControl : SignedQLogControl
    qLogValue : FiniteRational
open FullLearnerState public

record FullLearnerKernel (A : Nat) : Set₁ where
  constructor mkFullLearnerKernel
  field
    actionSpaceK : ActionSpace A
    watkinsKernel : WatkinsKernel A
    optimizerKernel : F4IntUKernel
    lcbKernel : LCBCountKernel
open FullLearnerKernel public

CanonicalFullLearnerState : Set₁
CanonicalFullLearnerState = FullLearnerState canonicalActionCount

CanonicalFullLearnerKernel : Set₁
CanonicalFullLearnerKernel = FullLearnerKernel canonicalActionCount

canonicalPolicy : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Fin A
canonicalPolicy K s = sparsemaxPolicy (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s))

canonicalPolicyWeight : ∀ {A} → FullLearnerKernel A → FullLearnerState A → SparseWeight
canonicalPolicyWeight K s = sparsemaxWeight (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s)) (canonicalPolicy K s)

canonicalPolicyWeightCode : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalPolicyWeightCode K s = int8OfNat (numerator (canonicalPolicyWeight K s))

HardSparse : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Set
HardSparse {A} K s =
  ∀ {a : Fin A} →
  a ≢ canonicalPolicy K s →
  numerator (sparsemaxWeight (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s)) a) ≡ zero

SoftSparseBounded : ∀ {A} →
  FullLearnerKernel A →
  FullLearnerState A →
  Nat →
  Set
SoftSparseBounded {A} K s epsilon =
  ∀ {a : Fin A} →
  a ≢ canonicalPolicy K s →
  numerator
    (sparsemaxWeight
      (actionSpaceK K)
      (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s)))
      (valuesCount (lcbCounts s))
      a)
  ≤ epsilon

hardSparse-to-softSparse-zero :
  ∀ {A}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A) →
  HardSparse K s →
  SoftSparseBounded K s zero
hardSparse-to-softSparse-zero K s h {a} distinct =
  subst
    (λ n → n ≤ zero)
    (sym (h distinct))
    z≤n

softSparse-zero-to-hardSparse :
  ∀ {A}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A) →
  SoftSparseBounded K s zero →
  HardSparse K s
softSparse-zero-to-hardSparse K s h {a} distinct =
  ≤-antisym (h distinct) z≤n

replaceNorm : ∀ {A} → FullLearnerState A → NormPair → FullLearnerState A
replaceNorm s n = fullLearnerState (clock s) (watkins s) (gru s) (optimizer s)
  n (lcbCounts s) (qLogControl s) (qLogValue s)

replaceOptimizer : ∀ {A} → FullLearnerState A → F4IntUState → FullLearnerState A
replaceOptimizer s o = fullLearnerState (clock s) (watkins s) (gru s) o
  (norm s) (lcbCounts s) (qLogControl s) (qLogValue s)

canonicalPolicy-norm-invariant :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : NormPair) →
  canonicalPolicy K (replaceNorm s n) ≡ canonicalPolicy K s
canonicalPolicy-norm-invariant K s n = refl

canonicalPolicy-optimizer-invariant :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (o : F4IntUState) →
  canonicalPolicy K (replaceOptimizer s o) ≡ canonicalPolicy K s
canonicalPolicy-optimizer-invariant K s o = refl

hardSparse-norm-optimizer-invariant :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : NormPair) (o : F4IntUState) →
  HardSparse K s →
  HardSparse K (replaceOptimizer (replaceNorm s n) o)
hardSparse-norm-optimizer-invariant K s n o h = h

hardSparse-composition-invariant :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : NormPair) (o : F4IntUState) →
  HardSparse K s →
  HardSparse K (replaceNorm (replaceOptimizer s o) n)
hardSparse-composition-invariant K s n o h = hardSparse-norm-optimizer-invariant K s n o h

hardSparse-composition-normPair-F4-L2 :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : NormPair) (o : F4IntUState) →
  HardSparse K s →
  HardSparse K (replaceNorm (replaceOptimizer s o) n)
hardSparse-composition-normPair-F4-L2 = hardSparse-composition-invariant

maxCriticValueList : List Int8 → Int8
maxCriticValueList [] = zero8
maxCriticValueList (x ∷ xs) with toℕ (code x) <ᵇ toℕ (code (maxCriticValueList xs))
... | true = maxCriticValueList xs
... | false = x

maxCriticValue8 : ∀ {A} → CriticState A → Int8
maxCriticValue8 q = maxCriticValueList (map (λ a → values q a) (finList _))

canonicalQLogBias : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalQLogBias K s = qLog2Bias8 (canonicalPolicyWeightCode K s)

canonicalReward8 : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalReward8 K s = canonicalPolicyWeightCode K s

canonicalDiscount8 : Int8
canonicalDiscount8 = one8

------------------------------------------------------------------------
-- Closed-loop endogenous feedback.
--
-- The Watkins target, GRU state, F4/L2 state, q-log control/value,
-- and count/policy channels form the canonical feedback loop.
------------------------------------------------------------------------

canonicalGRUFeedback : ∀ {A} → FullLearnerState A → Int8
canonicalGRUFeedback s = hiddenState (gru s)

canonicalF4L2Feedback : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalF4L2Feedback K s =
  int8Add
    (f4ThetaFull (optimizer s))
    (l2Correction (globalL2 (optimizerKernel K)))

canonicalQLogControlFeedback : ∀ {A} → FullLearnerState A → Int8
canonicalQLogControlFeedback s = coefficient (qLogControl s)

canonicalQLogValueFeedback : ∀ {A} → FullLearnerState A → Int8
canonicalQLogValueFeedback s = rationalCode (qLogValue s)

canonicalEndogenousFeedback : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalEndogenousFeedback K s =
  int8Add
    (canonicalGRUFeedback s)
    (int8Add
        (canonicalF4L2Feedback K s)
        (int8Add
          (canonicalQLogControlFeedback s)
          (canonicalQLogValueFeedback s))))

canonicalWatkinsTarget : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalWatkinsTarget K s =
  int8Add
    (int8Add
      (int8Add (canonicalReward8 K s) (canonicalQLogBias K s))
      (int8Mul canonicalDiscount8 (maxCriticValue8 (critic (watkins s)))))
    (canonicalEndogenousFeedback K s)

canonicalWatkinsTarget-law : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalWatkinsTarget K s ≡
  int8Add
    (int8Add
      (int8Add (canonicalReward8 K s) (canonicalQLogBias K s))
      (int8Mul canonicalDiscount8 (maxCriticValue8 (critic (watkins s)))))
    (canonicalEndogenousFeedback K s)
canonicalWatkinsTarget-law K s = refl

canonicalQLogControlStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → SignedQLogControl
canonicalQLogControlStep K s =
  signedQLogControl negativeAlpha8 (canonicalQLogBias K s)

canonicalSignal : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalSignal = canonicalWatkinsTarget

canonicalSignal-watkins-target : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalSignal K s ≡ canonicalWatkinsTarget K s
canonicalSignal-watkins-target K s = refl

canonicalWatkinsStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → WatkinsState A
canonicalWatkinsStep K s =
  watkinsStep (watkinsKernel K)
  (watkinsState (critic (watkins s)) (canonicalSignal K s) (trace (watkins s)))

canonicalGRUStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → GRUState
canonicalGRUStep K s =
  gruStep
    (gru s)
(canonicalSignal K s)

canonicalPersistentGRUPreservation : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistentGRUPreservation K s =
  persistent-preservation (gru s)
    (int8Add (canonicalSignal K s) (canonicalAttentionMix K s))

canonicalRecurrentInput-law : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalGRUStep K s ≡
  gruStep (gru s)
    (int8Add (canonicalSignal K s) (canonicalAttentionMix K s))
canonicalRecurrentInput-law K s = refl

canonicalOptimizerStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → F4IntUState
canonicalOptimizerStep K s = f4ThetaStep (optimizerKernel K) (optimizer s) (canonicalSignal K s)

canonicalOptimizerStep-qMunchausen-L2 : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalOptimizerStep K s ≡
  f4ThetaStep
    (optimizerKernel K)
    (optimizer s)
    (canonicalWatkinsTarget K s)
canonicalOptimizerStep-qMunchausen-L2 K s = refl

canonicalCountStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → LCBCountState A
canonicalCountStep K s = updateLCBCount (canonicalPolicy K s) (lcbCounts s)

canonicalQLogStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → FiniteRational
canonicalQLogStep K s = negativeFiniteQLog8 (canonicalPolicyWeightCode K s)

canonicalFullStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → FullLearnerState A
canonicalFullStep K s =
  fullLearnerState (suc (clock s))
  (canonicalWatkinsStep K s)
  (canonicalGRUStep K s)
  (canonicalOptimizerStep K s)
  (norm s)
  (canonicalCountStep K s)
  (canonicalQLogControlStep K s)
  (canonicalQLogStep K s)

canonicalFullStep-clock : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → clock (canonicalFullStep K s) ≡ suc (clock s)
canonicalFullStep-clock K s = refl

canonicalFullStep-watkins : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → watkins (canonicalFullStep K s) ≡ canonicalWatkinsStep K s
canonicalFullStep-watkins K s = refl

canonicalFullStep-gru : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → gru (canonicalFullStep K s) ≡ canonicalGRUStep K s
canonicalFullStep-gru K s = refl

canonicalFullStep-optimizer : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → optimizer (canonicalFullStep K s) ≡ canonicalOptimizerStep K s
canonicalFullStep-optimizer K s = refl

canonicalFullStep-norm : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → norm (canonicalFullStep K s) ≡ norm s
canonicalFullStep-norm K s = refl

canonicalFullStep-counts : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → lcbCounts (canonicalFullStep K s) ≡ canonicalCountStep K s
canonicalFullStep-counts K s = refl

canonicalFullStep-qLog : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → qLogValue (canonicalFullStep K s) ≡ canonicalQLogStep K s
canonicalFullStep-qLog K s = refl

canonicalFullStep-qLogControl : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → qLogControl (canonicalFullStep K s) ≡ canonicalQLogControlStep K s
canonicalFullStep-qLogControl K s = refl

canonicalNormPairWeightPlusOne-preservation : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  normPairWeightPlusOne (norm (canonicalFullStep K s)) ≡ normPairWeightPlusOne (norm s)
canonicalNormPairWeightPlusOne-preservation K s = refl

canonicalStep-not-fixed : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → canonicalFullStep K s ≢ s
canonicalStep-not-fixed K s eq =
  plus-suc-not-self (clock s) zero
    (trans (plus-suc (clock s) zero)
      (trans (cong suc (plus-zero (clock s)))
        (trans (sym (canonicalFullStep-clock K s))
          (cong (λ t → clock t) eq))))

canonicalTotalCountStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → totalCount (lcbCounts (canonicalFullStep K s)) ≡ suc (totalCount (lcbCounts s))
canonicalTotalCountStep K s = refl

canonicalNoFixedPoint :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalFullStep K s ≢ s
canonicalNoFixedPoint K s = canonicalStep-not-fixed K s

iterateCanonical : ∀ {A} → FullLearnerKernel A → Nat → FullLearnerState A → FullLearnerState A
iterateCanonical K zero s = s
iterateCanonical K (suc n) s = canonicalFullStep K (iterateCanonical K n s)

clockAfter : ∀ {A} (K : FullLearnerKernel A) (n : Nat) (s : FullLearnerState A) → clock (iterateCanonical K n s) ≡ clock s + n
clockAfter K zero s = sym (plus-zero (clock s))
clockAfter K (suc n) s = trans (cong suc (clockAfter K n s)) (sym (plus-suc (clock s) n))

canonicalAperiodic : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : Nat) → iterateCanonical K (suc n) s ≢ s
canonicalAperiodic K s n cyc = plus-suc-not-self (clock s) n
  (trans (sym (clockAfter K (suc n) s)) (cong clock cyc))

canonicalOrbitNonFixed : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : Nat) → iterateCanonical K n s ≢ canonicalFullStep K (iterateCanonical K n s)
canonicalOrbitNonFixed K s n eq =
  canonicalStep-not-fixed K (iterateCanonical K n s) (sym eq)

canonicalNoNontrivialFiniteCycle : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : Nat) → iterateCanonical K (suc n) s ≡ s → ⊥
canonicalNoNontrivialFiniteCycle K s n cyc = canonicalAperiodic K s n cyc

canonicalTotalCountIterate2 : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → totalCount (lcbCounts (iterateCanonical K 2 s)) ≡ suc (suc (totalCount (lcbCounts s)))
canonicalTotalCountIterate2 K s = refl

canonicalNoCountedTwoCycle : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → iterateCanonical K 2 s ≡ s → ⊥
canonicalNoCountedTwoCycle K s cyc = suc-suc-not-self (totalCount (lcbCounts s))
  (trans (sym (canonicalTotalCountIterate2 K s))
    (cong (λ t → totalCount (lcbCounts t)) cyc))

temperatureCodeLaw : sparsemaxTemperature ≡ 16
temperatureCodeLaw = refl

pessimisticInit : Int8
pessimisticInit = int8OfNat 128

pessimisticCritic : ∀ {A} → CriticState A
pessimisticCritic {A} = criticState (λ _ → pessimisticInit)

pessimisticCritic-law : ∀ {A} (i : Fin A) → values pessimisticCritic i ≡ pessimisticInit
pessimisticCritic-law i = refl

canonicalWalshBoundary : walshOrthonormal ≡ walshOrthonormal
canonicalWalshBoundary = refl

canonicalPersistent : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistent = canonicalPersistentGRUPreservation
