-- BEGIN MIRTH-SYNC GLOBAL OPTIONS
{-# OPTIONS
  --no-fast-reduce
  --lossy-unification
  --experimental-lazy-instances
  --confluence-check
  --auto-inline
  --guarded
  --exact-split
  --no-infer-absurd-clauses
  --no-projection-like
  --erased-matches
  --erase-record-parameters
#-}
-- END MIRTH-SYNC GLOBAL OPTIONS

------------------------------------------------------------------------
-- Canonical learner semantics.
--
-- This module is the executable/type-level source of the coupled learner:
-- recurrent monoid-LSTM state, Watkins state, custom q-projected sign-IDBD w/ coupled L2 optimizer state,
-- LCB counts, sparse policy readout, q-log state, the persistent learner channels, and the
-- endogenous feedback signal. The definitions below determine what the
-- learner actually does; theorem modules consume these definitions.
--
-- The main emergent facts are structural: LCB totalCount advances exactly
-- by one per canonical step, the optimizer state is explicit, the policy is
-- invariant under optimizer replacement, and the recurrent
-- components are exposed as composable monoid-LSTM state transitions. The integer
-- token layer and Haar-featured linear transformer are exact formal substrates, not
-- empirical language-model or physical-realism claims.
--
-- This file intentionally contains definitions and local definitional laws,
-- not economic existence conclusions. Convergence, fixed points, market
-- clearing, supporting prices, and Walrasian existence require independent
-- hypotheses and belong to the theorem/economic boundary documented outside
-- this module.
------------------------------------------------------------------------

module FullCoupled.CanonicalLearnerMonolith where

-- BEGIN MIRTH-SYNC COMMON IMPORTS
-- Merged external import surface; internal FullCoupled imports remain module-local.
open import Agda.Builtin.Reflection as Builtin
open import Addition
open import Cantor
open import Equality
open import Haskell.Law.Num.Def using (IsLawfulNum)
open import Haskell.Law.Num.Int using (iLawfulNumInt)
open import Haskell.Prelude hiding (String; ⊥)
open import InfinitePigeon.FinitePigeon
open import Iterative.Sets ua 𝓤
open import JK-LogicalFacts
open import JK-Monads
open import K-AC-N
open import Logic
open import LogicalFacts
open import MLTT.Spartan hiding (J)
open import MonadOnTypes.Definition
open import MonadOnTypes.J
open import MonadOnTypes.JK R
open import MonadOnTypes.K
open import Naturals
open import Naturals.Exponentiation
open import Naturals.Properties
open import Notation.Order
open import Order
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import W.Type
-- END MIRTH-SYNC COMMON IMPORTS

-- BEGIN MIRTH-SYNC CANONICAL COMMAND
-- "$AGDA_COMMAND" -i .
-- END MIRTH-SYNC CANONICAL COMMAND


record Int8 : Set where
  constructor int8
  field code : Int
open Int8 public

int8StateSpace : Set
int8StateSpace = Int

zero8 : Int8
zero8 = int8 (+ 0)

one8 : Int8
one8 = int8 (+ 1)

int8OfNat : Nat → Int8
int8OfNat n = int8 (+ n)

int8Add : Int8 → Int8 → Int8
int8Add x y = int8 (code x +Int code y)

int8Mul : Int8 → Int8 → Int8
int8Mul x y = int8 (code x *Int code y)

int8Neg : Int8 → Int8
int8Neg x = int8 (- code x)

int8Sub : Int8 → Int8 → Int8
int8Sub x y = int8 (code x +Int (- code y))

int8Roundtrip : ∀ n → code (int8OfNat n) ≡ + n
int8Roundtrip n = refl

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
  signedNeg : Nat → Signed
  signedZer : Signed
  signedPos : Nat → Signed

signedCode : Int8 → Signed
signedCode (int8 (+ 0)) = signedZer
signedCode (int8 (+ (suc n))) = signedPos (suc n)
signedCode (int8 (-[1+ n ])) = signedNeg (suc n)

data BoolLike : Set where
  enabled disabled : BoolLike

record ActionSpace (A : Set) : Set where
  constructor actionSpace
  field
    candidates : List Nat
    witness : Nat
open ActionSpace public

QFunction : ∀ {A : Set} → Set
QFunction {A} = Nat → Int8

CountFunction : ∀ {A : Set} → Set
CountFunction {A} = Nat → Nat

zeroQ : ∀ {A : Set} → QFunction {A}
zeroQ _ = zero8

zeroCounts : ∀ {A : Set} → CountFunction {A}
zeroCounts _ = zero

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

updateAt : ∀ {A : Set} → QFunction {A} → Nat → Int8 → QFunction {A}
updateAt q a r i with natEq i a
... | enabled = int8Add (q i) r
... | disabled = q i

incAt : ∀ {A : Set} → CountFunction {A} → Nat → CountFunction {A}
incAt c a i with natEq i a
... | enabled = suc (c i)
... | disabled = c i

record CriticState (A : Set) : Set where
  constructor criticState
  field values : QFunction {A}
open CriticState public

record WatkinsKernel (A : Set) : Set₁ where
  constructor mkWatkinsKernel
  field
    updateCritic : CriticState A → Int8 → CriticState A
    greedy : CriticState A → Int8 → BoolLike
    traceUpdate : BoolLike → BoolLike → BoolLike
open WatkinsKernel public

record WatkinsState (A : Set) : Set where
  constructor watkinsState
  field critic : CriticState A
        signal : Int8
        trace : BoolLike
open WatkinsState public

watkinsStep : ∀ {A : Set} → WatkinsKernel A → WatkinsState A → WatkinsState A
watkinsStep K s = watkinsState
  (updateCritic K (critic s) (signal s))
  (signal s)
  (traceUpdate K (trace s) (greedy K (critic s) (signal s)))

record LCBCountState (A : Set) : Set where
  constructor lcbCountState
  field valuesCount : CountFunction {A}
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
lcbNegate x = int8 (- code x)

scoreA : ∀ {A : Set} → QFunction {A} → CountFunction {A} → Nat → Int8
scoreA q c a = int8Add (q a) (lcbNegate (finiteLCBBonus8 (c a)))

lcbScore : ∀ {A : Set} → LCBCountKernel → LCBCountState A → CriticState A → QFunction {A}
lcbScore L c q a = int8Add (values q a) (lcbNegate (bonus L (valuesCount c a)))

sparsemaxTemperature : Nat
sparsemaxTemperature = 16

ScoreEntry : Set
ScoreEntry = Int8 × Nat

int8-code-injective : ∀ {x y : Int8} → code x ≡ code y → x ≡ y
int8-code-injective refl = refl

instance
  OrdInt8 : Ord Int8
  OrdInt8 = OrdBy int8-code-injective

ScoreEntryLess : ScoreEntry → ScoreEntry → Set
ScoreEntryLess (s₁ , a₁) (s₂ , a₂) =
  Either (s₁ > s₂) (s₁ ≡ s₂ × a₁ > a₂)

scoreEntryCompare : ∀ x y → Comparison ScoreEntryLess x y
scoreEntryCompare (s₁ , a₁) (s₂ , a₂) with compare s₁ s₂
... | less p = greater p
... | greater p = less p
... | equal refl with compare a₁ a₂
... | less p = greater p
... | greater p = less p
... | equal refl = equal refl

instance
  OrdScoreEntry : Ord ScoreEntry
  OrdScoreEntry = defaultOrd scoreEntryCompare

scoreList : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → List ScoreEntry
scoreList {A} K q c = map (λ a → (scoreA {A = A} q c a , a)) (candidates K)

sortScores : List ScoreEntry → List ScoreEntry
sortScores = sort

natAt : Nat → List Nat → Nat
natAt k [] = zero
natAt zero (x ∷ xs) = x
natAt (suc k) (x ∷ xs) = natAt k xs

sumList : List Nat → Nat
sumList [] = zero
sumList (x ∷ xs) = x + sumList xs

------------------------------------------------------------------------
-- Integer LayerNorm kernel.
--
-- Int8 is an exact Int wrapper.  The normalization arithmetic therefore
-- remains integral and the normalized output is represented as an exact
-- integer ratio.  A certificate supplies the non-zero square root of
-- the integer radicand; no floating-point approximation enters the
-- proof surface.
------------------------------------------------------------------------

integerCodeSum : List Int8 → Int
integerCodeSum [] = + 0
integerCodeSum (x ∷ xs) = code x +Int integerCodeSum xs

integerCodeSumList : List Int → Int
integerCodeSumList [] = + 0
integerCodeSumList (x ∷ xs) = x +Int integerCodeSumList xs

integerLayerNormCenteredNumerator :
  List Int8 → Int8 → Int
integerLayerNormCenteredNumerator xs x =
  (+ (length xs)) *Int code x +Int (- integerCodeSum xs)

integerLayerNormCenteredNumerators :
  List Int8 → List Int
integerLayerNormCenteredNumerators xs =
  map
    (λ x → integerLayerNormCenteredNumerator xs x)
    xs

integerLayerNormSquare : Int → Int
integerLayerNormSquare z = z *Int z

integerLayerNormVarianceNumerator :
  List Int8 → Int
integerLayerNormVarianceNumerator xs =
  integerCodeSumList
    (map
      integerLayerNormSquare
      (integerLayerNormCenteredNumerators xs))

integerLayerNormEpsilonContribution :
  List Int8 → Nat → Int
integerLayerNormEpsilonContribution xs epsilon =
  (+ (epsilon * (length xs) * (length xs)))

integerLayerNormRadicand :
  List Int8 → Nat → Int
integerLayerNormRadicand xs epsilon =
  integerLayerNormVarianceNumerator xs
  +Int
  integerLayerNormEpsilonContribution xs epsilon

record IntegerLayerNormConfig : Set where
  constructor integerLayerNormConfig
  field fixedScale gamma beta : Int8
open IntegerLayerNormConfig public

record IntegerLayerNormCertificate
  (xs : List Int8) : Set where
  constructor integerLayerNormCertificate
  field
    epsilon : Nat
    root : Nat
    rootSquared :
      (+ (root * root)) ≡
      integerLayerNormRadicand xs epsilon
    rootNonZero : root ≢ zero
open IntegerLayerNormCertificate public

record IntegerLayerNormValue : Set where
  constructor mkIntegerLayerNormValue
  field
    numerator : Int
    denominator : Nat
    denominatorNonZero : denominator ≢ zero
open IntegerLayerNormValue public

integerLayerNormValue :
  ∀ {xs : List Int8} →
  IntegerLayerNormConfig →
  IntegerLayerNormCertificate xs →
  Int8 →
  IntegerLayerNormValue
integerLayerNormValue {xs} config certificate x =
  mkIntegerLayerNormValue
    (code (gamma config) *Int
      (code (fixedScale config) *Int
        integerLayerNormCenteredNumerator xs x)
     +Int
     (code (beta config) *Int (+ (root certificate))))
    (root certificate)
    (rootNonZero certificate)


int8Magnitude : Int8 → Nat
int8Magnitude (int8 (+ n)) = n
int8Magnitude (int8 (-[1+ n ])) = suc n

topCodes : Nat → List ScoreEntry → List Nat
topCodes zero xs = []
topCodes (suc k) [] = []
topCodes (suc k) ((x , a) ∷ xs) = int8Magnitude x ∷ topCodes k xs

supportValid : List ScoreEntry → Nat → Nat → BoolLike
supportValid xs temperature k with natLt (sumList (topCodes k xs)) ((k * natAt (k ∸ 1) (topCodes k xs)) + temperature)
... | enabled = enabled
... | disabled = disabled

searchSupport : List ScoreEntry → Nat → Nat → Nat → Nat → Nat
searchSupport xs temperature zero current best = best
searchSupport xs temperature (suc n) current best with supportValid xs temperature current
... | enabled = searchSupport xs temperature n (suc current) (maxNat best current)
... | disabled = searchSupport xs temperature n (suc current) best

supportSize : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → Nat
supportSize K q c = searchSupport (sortScores (scoreList K q c)) sparsemaxTemperature (length (candidates K)) (suc zero) (suc zero)

record SparseWeight : Set where
  constructor sparseWeight
  field numerator denominator : Nat
open SparseWeight public

sparsemaxWeight : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → Nat → SparseWeight
sparsemaxWeight {A} K q c a = sparseWeight ((k * int8Magnitude (scoreA {A = A} q c a)) + sparsemaxTemperature ∸ s) (k * sparsemaxTemperature)
  where
    xs = sortScores (scoreList K q c)
    k = supportSize K q c
    s = sumList (topCodes k xs)

weightPositive : SparseWeight → BoolLike
weightPositive (sparseWeight n d) with natEq n zero
... | enabled = disabled
... | disabled = enabled

selectPositive : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → List ScoreEntry → Nat
selectPositive K q c [] = witness K
selectPositive K q c ((s , a) ∷ xs) with weightPositive (sparsemaxWeight K q c a)
... | enabled = a
... | disabled = selectPositive K q c xs

sparsemaxPolicy : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → Nat
sparsemaxPolicy K q c = selectPositive K q c (sortScores (scoreList K q c))

------------------------------------------------------------------------
-- Exact sparsemax behavior-policy readout.
-- The weight map is kept separate from the selected-action policy.
-- No probability normalization is claimed by this definition.
------------------------------------------------------------------------

updateLCBCount : ∀ {A : Set} → Nat → LCBCountState A → LCBCountState A
updateLCBCount {A} a (lcbCountState counts total) =
  lcbCountState (incAt {A = A} counts a) (suc total)

------------------------------------------------------------------------
-- TypeTopology Rationals supplies the canonical exact rational carrier.
-- The legacy Dyadic helper names remain stable for theorem/registry
-- surfaces, but their carrier is now TypeTopology's rational type.
------------------------------------------------------------------------

Dyadic : Set
Dyadic = ℚ

fromNatDyadic : Nat → Nat → Dyadic
fromNatDyadic n exponent =
  toℚ (pos n , exponent)

dyadicNumerator : Dyadic → Nat
dyadicNumerator ((pos n , d) , _) = n
dyadicNumerator ((negsucc n , d) , _) = zero

dyadicDenominator : Dyadic → Nat
dyadicDenominator ((z , d) , _) =
  succ d

qLog8 : Int8 → Dyadic
qLog8 x with int8Magnitude x
... | zero = fromNatDyadic 1 zero
... | suc n = fromNatDyadic (128 ∸ suc n) (suc n)

munchausenScale8 : Nat
munchausenScale8 = 16

signedDyadicBias8 : Dyadic → Int8
signedDyadicBias8 q with dyadicNumerator q
... | zero = zero8
... | suc n = int8Neg
  (int8OfNat
    (Data.Nat._/_
      (munchausenScale8 * suc n)
      (dyadicDenominator q)))

qLog2Bias8 : Int8 → Int8
qLog2Bias8 x =
  signedDyadicBias8 (qLog8 x)

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

data HardSign : Set where
  negativeSign zeroSign positiveSign : HardSign

hardSignNonnegative : Int8 → HardSign
hardSignNonnegative (int8 (+ 0)) = zeroSign
hardSignNonnegative (int8 (+ (suc n))) = positiveSign
hardSignNonnegative (int8 (-[1+ n ])) = negativeSign

hardSign : Int8 → HardSign
hardSign (int8 (+ 0)) = zeroSign
hardSign (int8 (+ (suc n))) = positiveSign
hardSign (int8 (-[1+ n ])) = negativeSign

hardSignGate : Int8 → Int8
hardSignGate x with hardSign x
... | negativeSign = int8OfNat 255
... | zeroSign = zero8
... | positive = one8

two8 : Int8
two8 = int8Add one8 one8

relu8 : Int8 → Int8
relu8 x with hardSign x
... | negativeSign = zero8
... | zeroSign = zero8
... | positive = x

leaky2 : Int8 → Int8
leaky2 x with hardSign x
... | negativeSign = int8Mul two8 x
... | zeroSign = zero8
... | positive = x

------------------------------------------------------------------------
-- Monoid LSTM recurrent core.
--
-- One input acts as an affine endomorphism of cell state.  Affine
-- composition is the carrier monoid; recurrent prefixes therefore admit
-- exact scan composition.  Hidden state is derived from the new cell
-- state plus the signed input feature.  Persistent matrix/noise/control
-- channels remain explicit learner state, preserving the old theorem
-- surface needed by downstream modules without retaining GRU dynamics.
------------------------------------------------------------------------

record MonoidLSTMMatrices : Set where
  constructor monoidLSTMMatrices
  field matrixZ matrixR matrixH : Int8
open MonoidLSTMMatrices public

record MonoidLSTMNoise : Set where
  constructor monoidLSTMNoise
  field noiseZ noiseR noiseH : Int8
open MonoidLSTMNoise public

record MonoidLSTMControl : Set where
  constructor monoidLSTMControl
  field optimizerToken l2Token : Int8
open MonoidLSTMControl public

record MonoidAffine : Set where
  constructor monoidAffine
  field slope offset : Int8
open MonoidAffine public

_∘ₘ_ : MonoidAffine → MonoidAffine → MonoidAffine
(a₁ , b₁) ∘ₘ (a₂ , b₂) =
  int8Mul a₁ a₂ ,
  int8Add (int8Mul a₁ b₂) b₁

monoidAffine-id : MonoidAffine
monoidAffine-id = one8 , zero8

monoidAffine-assoc : ∀ a b c → (a ∘ₘ b) ∘ₘ c ≡ a ∘ₘ (b ∘ₘ c)
monoidAffine-assoc (a₁ , b₁) (a₂ , b₂) (a₃ , b₃) =
  cong₂ _,_
    (int8*-assoc a₁ a₂ a₃)
    (trans
      (cong₂ int8Add
        (int8*-assoc a₁ a₂ b₃)
        refl)
      (trans
        (sym (int8+-assoc
          (int8Mul a₁ (int8Mul a₂ b₃))
          (int8Mul a₁ b₂)
          b₁))
        (cong
          (λ z → int8Add z b₁)
          (sym (int8*-distribˡ
            a₁
            (int8Mul a₂ b₃)
            b₂)))))

monoidAffine-idˡ : ∀ a → monoidAffine-id ∘ₘ a ≡ a
monoidAffine-idˡ (a , b) =
  cong₂ _,_
    (int8*-idˡ a)
    (trans
      (cong (λ z → int8Add z zero8) (int8*-idˡ b))
      (int8+-idʳ b))

monoidAffine-idʳ : ∀ a → a ∘ₘ monoidAffine-id ≡ a
monoidAffine-idʳ (a , b) =
  cong₂ _,_
    (int8*-idʳ a)
    (trans
      (cong (λ z → int8Add z b) (int8*-zeroʳ a))
      (int8+-idˡ b))

applyMonoidAffine : MonoidAffine → Int8 → Int8
applyMonoidAffine (a , b) c =
  int8Add (int8Mul a c) b

data MonoidLSTMGate : Set where
  monoidHold monoidWrite monoidReset monoidAccum : MonoidLSTMGate

monoidLSTMGateOf : Int8 → MonoidLSTMGate
monoidLSTMGateOf (int8 (+ 0)) = monoidHold
monoidLSTMGateOf (int8 (+ (suc n))) = monoidAccum
monoidLSTMGateOf (int8 (-[1+ n ])) = monoidReset

monoidLSTMCellStep : MonoidLSTMGate → Int8 → Int8 → Int8
monoidLSTMCellStep monoidHold c x = c
monoidLSTMCellStep monoidWrite c x = leaky2 x
monoidLSTMCellStep monoidReset c x = zero8
monoidLSTMCellStep monoidAccum c x = int8Add c (leaky2 x)

monoidLSTMAffineOf : MonoidLSTMGate → Int8 → MonoidAffine
monoidLSTMAffineOf monoidHold x = one8 , zero8
monoidLSTMAffineOf monoidWrite x = zero8 , leaky2 x
monoidLSTMAffineOf monoidReset x = zero8 , zero8
monoidLSTMAffineOf monoidAccum x = one8 , leaky2 x

monoidLSTMCellStep-is-affine :
  ∀ g c x →
  monoidLSTMCellStep g c x ≡
  applyMonoidAffine (monoidLSTMAffineOf g x) c
monoidLSTMCellStep-is-affine monoidHold c x = refl
monoidLSTMCellStep-is-affine monoidWrite c x = refl
monoidLSTMCellStep-is-affine monoidReset c x = refl
monoidLSTMCellStep-is-affine monoidAccum c x = refl

scanMonoidAffine : List Int8 → MonoidAffine
scanMonoidAffine [] = monoidAffine-id
scanMonoidAffine (x ∷ xs) =
  scanMonoidAffine xs ∘ₘ monoidLSTMAffineOf (monoidLSTMGateOf x) x

scanMonoidAffine-cons :
  ∀ x xs →
  scanMonoidAffine (x ∷ xs) ≡
  scanMonoidAffine xs ∘ₘ monoidLSTMAffineOf (monoidLSTMGateOf x) x
scanMonoidAffine-cons x xs = refl

runMonoidLSTMCell : List Int8 → Int8 → Int8
runMonoidLSTMCell xs c₀ =
  applyMonoidAffine (scanMonoidAffine xs) c₀

record MonoidLSTMState : Set where
  constructor monoidLSTMState
  field
    hiddenState : Int8
    cellState : Int8
    matrixState : MonoidLSTMMatrices
    noiseState : MonoidLSTMNoise
    controlState : MonoidLSTMControl
open MonoidLSTMState public

identityMonoidLSTMMatrices : MonoidLSTMMatrices
identityMonoidLSTMMatrices = monoidLSTMMatrices one8 one8 one8

zeroMonoidLSTMNoise : MonoidLSTMNoise
zeroMonoidLSTMNoise = monoidLSTMNoise zero8 zero8 zero8

zeroMonoidLSTMControl : MonoidLSTMControl
zeroMonoidLSTMControl = monoidLSTMControl zero8 zero8

monoidLSTMHiddenStep : Int8 → Int8 → Int8 → Int8
monoidLSTMHiddenStep h c x =
  int8Add c (leaky2 (int8Add h x))

monoidLSTMStep : MonoidLSTMState → Int8 → MonoidLSTMState
monoidLSTMStep
  (monoidLSTMState h c m n g)
  x =
  let c₁ = monoidLSTMCellStep (monoidLSTMGateOf x) c x
      h₁ = monoidLSTMHiddenStep h c₁ x
  in monoidLSTMState h₁ c₁ m n g

persistentMonoidLSTM :
  MonoidLSTMState →
  MonoidLSTMMatrices × (MonoidLSTMNoise × MonoidLSTMControl)
persistentMonoidLSTM (monoidLSTMState h c m n g) = m , (n , g)

persistentMonoidLSTM-preservation :
  ∀ (s : MonoidLSTMState) (x : Int8) →
  persistentMonoidLSTM (monoidLSTMStep s x) ≡
  persistentMonoidLSTM s
persistentMonoidLSTM-preservation
  (monoidLSTMState h c m n g) x = refl

monoidLSTMParameterPersistence :
  ∀ (s : MonoidLSTMState) (x : Int8) →
  matrixState (monoidLSTMStep s x) ≡ matrixState s ×
  noiseState (monoidLSTMStep s x) ≡ noiseState s ×
  controlState (monoidLSTMStep s x) ≡ controlState s
monoidLSTMParameterPersistence
  (monoidLSTMState h c m n g) x =
  refl , (refl , refl)

MonoidLSTMEquivalent : MonoidLSTMState → MonoidLSTMState → Set
MonoidLSTMEquivalent s t =
  persistentMonoidLSTM s ≡ persistentMonoidLSTM t

monoidLSTMStep-respects-equivalence :
  ∀ (s t : MonoidLSTMState) (x : Int8) →
  MonoidLSTMEquivalent s t →
  MonoidLSTMEquivalent (monoidLSTMStep s x) (monoidLSTMStep t x)
monoidLSTMStep-respects-equivalence s t x eq =
  trans
    (persistentMonoidLSTM-preservation s x)
    (trans eq (sym (persistentMonoidLSTM-preservation t x)))

------------------------------------------------------------------------
-- Compatibility surface for downstream theorem modules.
-- GRU names are legacy aliases; canonical semantics are MonoidLSTM.
------------------------------------------------------------------------

GRUMatrices : Set
GRUMatrices = MonoidLSTMMatrices

GRUNoise : Set
GRUNoise = MonoidLSTMNoise

GlobalControl : Set
GlobalControl = MonoidLSTMControl

GRUState : Set
GRUState = MonoidLSTMState

gruMatrices : Int8 → Int8 → Int8 → GRUMatrices
gruMatrices a b c = monoidLSTMMatrices a b c

gruNoise : Int8 → Int8 → Int8 → GRUNoise
gruNoise a b c = monoidLSTMNoise a b c

mkGlobalControl : Int8 → Int8 → GlobalControl
mkGlobalControl a b = monoidLSTMControl a b

gruState :
  Int8 →
  Int8 →
  MonoidLSTMMatrices →
  MonoidLSTMNoise →
  MonoidLSTMControl →
  MonoidLSTMState
gruState = monoidLSTMState

identityGRUMatrices : GRUMatrices
identityGRUMatrices = identityMonoidLSTMMatrices

zeroGRUNoise : GRUNoise
zeroGRUNoise = zeroMonoidLSTMNoise

zeroGlobalControl : GlobalControl
zeroGlobalControl = zeroMonoidLSTMControl

dyadicCode : Dyadic → Int8
dyadicCode q = int8OfNat (dyadicNumerator q)

identityActivation8 : Int8 → Int8
identityActivation8 x = x

identityActivation8-law : ∀ x → identityActivation8 x ≡ x
identityActivation8-law x = refl

identityActivation8-zero : identityActivation8 zero8 ≡ zero8
identityActivation8-zero = refl

gruCandidate8 : Int8 → Int8 → Int8
gruCandidate8 h x = int8Add h x

complement128 : Int8 → Int8
complement128 g = int8Sub one8 g

mix8 : Int8 → Int8 → Int8 → Int8
mix8 g old new =
  int8Add
    (int8Mul (complement128 g) old)
    (int8Mul g new)

gateCode : Signed → Int8
gateCode (signedNeg n) = zero8
gateCode signedZer = zero8
gateCode (signedPos n) = one8

gateFromInput : Int8 → Int8
gateFromInput x = gateCode (signedCode x)

monoidLSTMRecurrentStep : MonoidLSTMState → Int8 → MonoidLSTMState
monoidLSTMRecurrentStep = monoidLSTMStep

gruStep : GRUState → Int8 → GRUState
gruStep = monoidLSTMStep

persistentGRU :
  GRUState →
  GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU = persistentMonoidLSTM

persistent-preservation :
  ∀ (s : GRUState) (x : Int8) →
  persistentGRU (gruStep s x) ≡ persistentGRU s
persistent-preservation s x =
  persistentMonoidLSTM-preservation s x

gruParameterPersistence :
  ∀ (s : GRUState) (x : Int8) →
  matrixState (gruStep s x) ≡ matrixState s ×
  noiseState (gruStep s x) ≡ noiseState s ×
  controlState (gruStep s x) ≡ controlState s
gruParameterPersistence s x =
  monoidLSTMParameterPersistence s x

GRUEquivalent : GRUState → GRUState → Set
GRUEquivalent = MonoidLSTMEquivalent

gruEquivalent-refl : ∀ s → GRUEquivalent s s
gruEquivalent-refl = monoidLSTMEquivalent-refl
  where
    monoidLSTMEquivalent-refl : ∀ s → MonoidLSTMEquivalent s s
    monoidLSTMEquivalent-refl s = refl

gruStep-respects-equivalence :
  ∀ (s t : GRUState) (x : Int8) →
  GRUEquivalent s t →
  GRUEquivalent (gruStep s x) (gruStep t x)
gruStep-respects-equivalence =
  monoidLSTMStep-respects-equivalence

record GRUAction : Set₁ where
  constructor gruAction
  field runGRU : GRUState → GRUState
open GRUAction public

identityGRUAction : GRUAction
identityGRUAction = gruAction (λ s → s)

composeGRUAction : GRUAction → GRUAction → GRUAction
composeGRUAction f g =
  gruAction (λ s → runGRU f (runGRU g s))

gruActionAssociativity : ∀ f g h s →
  runGRU
    (composeGRUAction (composeGRUAction f g) h) s ≡
  runGRU
    (composeGRUAction f (composeGRUAction g h)) s
gruActionAssociativity f g h s = refl

inputGRUAction : Int8 → GRUAction
inputGRUAction x = gruAction (λ s → monoidLSTMStep s x)

record RecurrentNetwork (State Input : Set) : Set₁ where
  constructor recurrentNetwork
  field
    runNetwork : State → Input → State
open RecurrentNetwork public

canonicalMonoidLSTMRecurrentNetwork :
  RecurrentNetwork MonoidLSTMState Int8
canonicalMonoidLSTMRecurrentNetwork =
  recurrentNetwork monoidLSTMStep

canonicalMonoidLSTMNetwork-law :
  ∀ (s : MonoidLSTMState) (x : Int8) →
  runNetwork canonicalMonoidLSTMRecurrentNetwork s x ≡
  monoidLSTMStep s x
canonicalMonoidLSTMNetwork-law s x = refl

canonicalGRURecurrentNetwork : RecurrentNetwork GRUState Int8
canonicalGRURecurrentNetwork =
  recurrentNetwork gruStep

canonicalGRUNetwork-law :
  ∀ (s : GRUState) (x : Int8) →
  runNetwork canonicalGRURecurrentNetwork s x ≡
  monoidLSTMStep s x
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

canonicalMonoidLSTM-recurrent-prefix-correct :
  ∀ (xs : Nat → Int8) (n : Nat) (s : MonoidLSTMState) →
  applyEndomorphism
    (recurrentPrefixEndomorphism
      canonicalMonoidLSTMRecurrentNetwork
      xs
      n)
    s
  ≡
  recurrentPrefixState
    canonicalMonoidLSTMRecurrentNetwork
    xs
    n
    s
canonicalMonoidLSTM-recurrent-prefix-correct =
  recurrentPrefix-correct canonicalMonoidLSTMRecurrentNetwork

canonicalMonoidLSTM-recurrent-prefix-split :
  ∀ (xs : Nat → Int8) (m n : Nat) (s : MonoidLSTMState) →
  recurrentPrefixState
    canonicalMonoidLSTMRecurrentNetwork
    xs
    (m + n)
    s
  ≡
  recurrentPrefixState
    canonicalMonoidLSTMRecurrentNetwork
    (shiftInput xs m)
    n
    (recurrentPrefixState
      canonicalMonoidLSTMRecurrentNetwork
      xs
      m
      s)
canonicalMonoidLSTM-recurrent-prefix-split =
  recurrentPrefix-split canonicalMonoidLSTMRecurrentNetwork

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

gruInputActionAssociativity :
  ∀ x y z s →
  runGRU
    (composeGRUAction
      (composeGRUAction
        (inputGRUAction x)
        (inputGRUAction y))
      (inputGRUAction z))
    s
  ≡
  runGRU
    (composeGRUAction
      (inputGRUAction x)
      (composeGRUAction
        (inputGRUAction y)
        (inputGRUAction z)))
    s
gruInputActionAssociativity x y z s = refl


gruStateInt8CoordinateCount : Nat
gruStateInt8CoordinateCount = 10

criticInt8CoordinateCount : Nat
criticInt8CoordinateCount = 2

gruPersistentQuotientCoordinateCount : Nat
gruPersistentQuotientCoordinateCount = 8

fullLearnerInt8CoordinateCount : Nat
fullLearnerInt8CoordinateCount = 24

fullLearnerInt8CoordinateCount-law : fullLearnerInt8CoordinateCount ≡ 24
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

record FullLearnerState (A : Set) : Set₁ where
  constructor fullLearnerState
  field
    watkins : WatkinsState A
    gru : GRUState
    optimizer : F4IntUState
    lcbCounts : LCBCountState A
    qLogControl : SignedQLogControl
    qLogValue : Dyadic
    haarAccumulator : HaarAccumulator
open FullLearnerState public

record FullLearnerKernel (A : Set) : Set₁ where
  constructor mkFullLearnerKernel
  field
    actionSpaceK : ActionSpace A
    watkinsKernel : WatkinsKernel A
    optimizerKernel : F4IntUKernel
    lcbKernel : LCBCountKernel
open FullLearnerKernel public

CanonicalFullLearnerState : Set₁
CanonicalFullLearnerState = FullLearnerState ⊤

CanonicalFullLearnerKernel : Set₁
CanonicalFullLearnerKernel = FullLearnerKernel ⊤

canonicalPolicy : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → Nat
canonicalPolicy K s = sparsemaxPolicy (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s))

canonicalPolicyWeight : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → SparseWeight
canonicalPolicyWeight K s = sparsemaxWeight (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s)) (canonicalPolicy K s)

canonicalPolicyWeightCode : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → Int8

BehaviorPolicy : Set
BehaviorPolicy = Nat → SparseWeight

canonicalBehaviorPolicy :
  ∀ {A : Set} →
  FullLearnerKernel A →
  FullLearnerState A →
  BehaviorPolicy
canonicalBehaviorPolicy K s a =
  sparsemaxWeight
    (actionSpaceK K)
    (lcbScore
      (lcbKernel K)
      (lcbCounts s)
      (critic (watkins s)))
    (valuesCount (lcbCounts s))
    a

canonicalBehaviorAction :
  ∀ {A : Set} →
  FullLearnerKernel A →
  FullLearnerState A →
  Nat
canonicalBehaviorAction K s = canonicalPolicy K s

canonicalBehaviorAction-law :
  ∀ {A : Set}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A) →
  canonicalBehaviorAction K s ≡ canonicalPolicy K s
canonicalBehaviorAction-law K s = refl

canonicalPolicyWeightCode K s = int8OfNat (numerator (canonicalPolicyWeight K s))

HardSparse : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → Set
HardSparse {A} K s =
  ∀ {a : Nat} →
  a ≢ canonicalPolicy K s →
  numerator (sparsemaxWeight (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s)) a) ≡ zero

SoftSparseBounded : ∀ {A : Set} →
  FullLearnerKernel A →
  FullLearnerState A →
  Nat →
  Set
SoftSparseBounded {A} K s epsilon =
  ∀ {a : Nat} →
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

replaceOptimizer : ∀ {A} → FullLearnerState A → F4IntUState → FullLearnerState A
replaceOptimizer s o = fullLearnerState (watkins s) (gru s) o
  (lcbCounts s) (qLogControl s) (qLogValue s) (haarAccumulator s)

canonicalPolicy-optimizer-invariant :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (o : F4IntUState) →
  canonicalPolicy K (replaceOptimizer s o) ≡ canonicalPolicy K s
canonicalPolicy-optimizer-invariant K s o = refl

maxCriticValueList : List Int8 → Int8
maxCriticValueList [] = zero8
maxCriticValueList (x ∷ xs) with code x ≤? code (maxCriticValueList xs)
... | Relation.Nullary.yes _ = maxCriticValueList xs
... | Relation.Nullary.no _ = x

maxCriticValue8 : ∀ {A : Set} → ActionSpace A → CriticState A → Int8
maxCriticValue8 K q = maxCriticValueList (map (λ a → values q a) (candidates K))

canonicalQLogBias : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalQLogBias K s = qLog2Bias8 (canonicalPolicyWeightCode K s)

canonicalReward8 : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalReward8 K s = canonicalPolicyWeightCode K s

canonicalDiscount8 : Int8
canonicalDiscount8 = one8

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
canonicalQLogValueFeedback s = dyadicCode (qLogValue s)

canonicalEndogenousFeedback : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalEndogenousFeedback K s =
  int8Add
    (canonicalGRUFeedback s)
    (int8Add
        (canonicalF4L2Feedback K s)
        (int8Add
          (canonicalQLogControlFeedback s)
          (canonicalQLogValueFeedback s)))

canonicalWatkinsTarget : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalWatkinsTarget K s =
  int8Add
    (int8Add
      (int8Add (canonicalReward8 K s) (canonicalQLogBias K s))
      (int8Mul canonicalDiscount8 (maxCriticValue8 (actionSpaceK K) (critic (watkins s)))))
    (canonicalEndogenousFeedback K s)

canonicalWatkinsTarget-law : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalWatkinsTarget K s ≡
  int8Add
    (int8Add
      (int8Add (canonicalReward8 K s) (canonicalQLogBias K s))
      (int8Mul canonicalDiscount8 (maxCriticValue8 (actionSpaceK K) (critic (watkins s)))))
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

canonicalHaarAccumulatorStep :
  ∀ {A} →
  FullLearnerKernel A →
  FullLearnerState A →
  HaarAccumulator
canonicalHaarAccumulatorStep K s =
  haarAccumulatorStep
    canonicalHaarFeaturedTransformer
    (haarAccumulator s)
    (canonicalSignal K s)

canonicalHaarRecurrentInput :
  ∀ {A} →
  FullLearnerKernel A →
  FullLearnerState A →
  Int8
canonicalHaarRecurrentInput K s =
  haarQueryRead
    canonicalHaarFeaturedTransformer
    (canonicalHaarAccumulatorStep K s)
    (canonicalSignal K s)

canonicalGRUStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → GRUState
canonicalGRUStep K s =
  gruStep
    (gru s)
    (canonicalHaarRecurrentInput K s)

canonicalPersistentGRUPreservation : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistentGRUPreservation K s =
  persistent-preservation (gru s)
    (canonicalSignal K s)

canonicalRecurrentInput-law : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalGRUStep K s ≡
  gruStep (gru s)
    (canonicalSignal K s)
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

canonicalQLogStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → Dyadic
canonicalQLogStep K s = qLog8 (canonicalPolicyWeightCode K s)

canonicalFullStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → FullLearnerState A
canonicalFullStep K s =
  fullLearnerState (canonicalWatkinsStep K s)
  (canonicalGRUStep K s)
  (canonicalOptimizerStep K s)
  (canonicalCountStep K s)
  (canonicalQLogControlStep K s)
  (canonicalQLogStep K s)
  (canonicalHaarAccumulatorStep K s)

canonicalFullStep-watkins : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → watkins (canonicalFullStep K s) ≡ canonicalWatkinsStep K s
canonicalFullStep-watkins K s = refl

canonicalFullStep-gru : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → gru (canonicalFullStep K s) ≡ canonicalGRUStep K s
canonicalFullStep-gru K s = refl

canonicalFullStep-optimizer : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → optimizer (canonicalFullStep K s) ≡ canonicalOptimizerStep K s
canonicalFullStep-optimizer K s = refl

canonicalFullStep-counts : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → lcbCounts (canonicalFullStep K s) ≡ canonicalCountStep K s
canonicalFullStep-counts K s = refl

canonicalFullStep-qLog : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → qLogValue (canonicalFullStep K s) ≡ canonicalQLogStep K s
canonicalFullStep-qLog K s = refl

canonicalFullStep-qLogControl : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → qLogControl (canonicalFullStep K s) ≡ canonicalQLogControlStep K s
canonicalFullStep-qLogControl K s = refl

canonicalTotalCountStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → totalCount (lcbCounts (canonicalFullStep K s)) ≡ suc (totalCount (lcbCounts s))
canonicalTotalCountStep K s = refl

canonicalNoFixedPoint :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalFullStep K s ≢ s
canonicalNoFixedPoint K s eq =
  plus-suc-not-self (totalCount (lcbCounts s)) zero
    (trans (plus-suc (totalCount (lcbCounts s)) zero)
      (trans (cong suc (plus-zero (totalCount (lcbCounts s))))
        (trans (sym (canonicalTotalCountStep K s))
          (cong (λ t → totalCount (lcbCounts t)) eq))))

iterateCanonical : ∀ {A} → FullLearnerKernel A → Nat → FullLearnerState A → FullLearnerState A
iterateCanonical K zero s = s
iterateCanonical K (suc n) s = canonicalFullStep K (iterateCanonical K n s)

canonicalTotalCountAfter :
  ∀ {A} (K : FullLearnerKernel A) (n : Nat) (s : FullLearnerState A) →
  totalCount (lcbCounts (iterateCanonical K n s)) ≡
  totalCount (lcbCounts s) + n
canonicalTotalCountAfter K zero s = sym (plus-zero (totalCount (lcbCounts s)))
canonicalTotalCountAfter K (suc n) s =
  trans
    (canonicalTotalCountStep K (iterateCanonical K n s))
    (trans
      (cong suc (canonicalTotalCountAfter K n s))
      (sym (plus-suc (totalCount (lcbCounts s)) n)))

canonicalAperiodic : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : Nat) → iterateCanonical K (suc n) s ≢ s
canonicalAperiodic K s n cyc = plus-suc-not-self (totalCount (lcbCounts s)) n
  (trans
    (sym (canonicalTotalCountAfter K (suc n) s))
    (cong (λ t → totalCount (lcbCounts t)) cyc))

canonicalOrbitNonFixed : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : Nat) → iterateCanonical K n s ≢ canonicalFullStep K (iterateCanonical K n s)
canonicalOrbitNonFixed K s n eq =
  canonicalNoFixedPoint K (iterateCanonical K n s) (sym eq)

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

pessimisticCritic-law : ∀ {A} (i : Nat) → values (pessimisticCritic {A = A}) i ≡ pessimisticInit
pessimisticCritic-law {A = A} i = refl

canonicalPersistent : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistent = canonicalPersistentGRUPreservation

CanonicalToken : Set
CanonicalToken = Int

CanonicalTokenSequence : Set
CanonicalTokenSequence = List CanonicalToken

canonicalTokenEncode : CanonicalToken → Int8
canonicalTokenEncode = int8

canonicalTokenEncodeList : CanonicalTokenSequence → List Int8
canonicalTokenEncodeList = map canonicalTokenEncode

canonicalTokenStep : GRUState → CanonicalToken → GRUState
canonicalTokenStep s t = gruStep s (canonicalTokenEncode t)

canonicalTokenRecurrentNetwork :
  RecurrentNetwork GRUState CanonicalToken
canonicalTokenRecurrentNetwork =
  recurrentNetwork canonicalTokenStep

recurrentListState :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  List Input →
  State →
  State
recurrentListState R [] s = s
recurrentListState R (x ∷ xs) s =
  recurrentListState R xs (runNetwork R s x)

canonicalTokenListState :
  CanonicalTokenSequence →
  GRUState →
  GRUState
canonicalTokenListState [] s = s
canonicalTokenListState (t ∷ ts) s =
  canonicalTokenListState ts (canonicalTokenStep s t)

CanonicalTokenLogitVector : Set
CanonicalTokenLogitVector = CanonicalToken → Int8

record CanonicalTokenLanguageModelKernel : Set₁ where
  constructor canonicalTokenLanguageModelKernel
  field
    logits : GRUState → CanonicalTokenLogitVector
open CanonicalTokenLanguageModelKernel public

canonicalTokenLogitTrace :
  CanonicalTokenLanguageModelKernel →
  CanonicalTokenSequence →
  GRUState →
  List CanonicalTokenLogitVector
canonicalTokenLogitTrace K [] s = []
canonicalTokenLogitTrace K (t ∷ ts) s =
  logits K s ∷
  canonicalTokenLogitTrace K ts (canonicalTokenStep s t)

------------------------------------------------------------------------
-- Haar-featured linear transformer.
--
-- Haar mixing remains exact integer arithmetic, now used as a feature map
-- inside a parameterized linear-attention accumulator.  The accumulator
-- is additive and therefore itself forms a monoid; sequence processing is
-- a pure left-to-right scan over rank-one feature updates.
------------------------------------------------------------------------

CanonicalHaarPair : Set
CanonicalHaarPair = Int8 × Int8

canonicalHaarMix : Int8 → Int8 → CanonicalHaarPair
canonicalHaarMix x y =
  int8Add x y , int8Sub x y

canonicalHaarMix-left : ∀ x y →
  proj₁ (canonicalHaarMix x y) ≡ int8Add x y
canonicalHaarMix-left x y = refl

canonicalHaarMix-right : ∀ x y →
  proj₂ (canonicalHaarMix x y) ≡ int8Sub x y
canonicalHaarMix-right x y = refl

canonicalHaarMix-linear-form :
  ∀ x y →
  canonicalHaarMix x y ≡
  (int8Add x y , int8Sub x y)
canonicalHaarMix-linear-form x y = refl

canonicalReLU8 : Int8 → Int8
canonicalReLU8 x with hardSign x
... | negativeSign = zero8
... | zeroSign = zero8
... | positiveSign = x

canonicalCReLU8 : Int8 → CanonicalHaarPair
canonicalCReLU8 x =
  canonicalReLU8 x , canonicalReLU8 (int8Neg x)

------------------------------------------------------------------------
-- Rational CReLU': CReLU with the negative ReLU branch replaced by the
-- exact rational softsign branch, matching the SignReLU shape while
-- keeping the paired positive/negative CReLU representation.
------------------------------------------------------------------------

canonicalSignReLU' : ℚ → ℚ
canonicalSignReLU' (((negsucc n , a) , _)) =
  toℚ (negsucc n , a + succ n)
canonicalSignReLU' q = q

CanonicalCReLUPrimePair : Set
CanonicalCReLUPrimePair = ℚ × ℚ

canonicalCReLU' : ℚ → CanonicalCReLUPrimePair
canonicalCReLU' x =
  canonicalSignReLU' x , canonicalSignReLU' (- x)

canonicalHaarFeature : Int8 → CanonicalHaarPair
canonicalHaarFeature x =
  canonicalHaarMix
    (proj₁ (canonicalCReLU8 x))
    (proj₂ (canonicalCReLU8 x))

canonicalHaarFeature-left : ∀ x →
  proj₁ (canonicalHaarFeature x) ≡
  int8Add
    (proj₁ (canonicalCReLU8 x))
    (proj₂ (canonicalCReLU8 x))
canonicalHaarFeature-left x = refl

canonicalHaarFeature-right : ∀ x →
  proj₂ (canonicalHaarFeature x) ≡
  int8Sub
    (proj₁ (canonicalCReLU8 x))
    (proj₂ (canonicalCReLU8 x))
canonicalHaarFeature-right x = refl

canonicalHaarOrthogonalCross :
  int8Add
    (int8Mul one8 one8)
    (int8Mul one8 (int8Neg one8))
  ≡ zero8
canonicalHaarOrthogonalCross = refl

canonicalHaarFeatureReconstruct :
  ∀ x →
  let p = proj₁ (canonicalCReLU8 x)
      n = proj₂ (canonicalCReLU8 x)
  in int8Sub p n ≡ x
canonicalHaarFeatureReconstruct
  (int8 (+ 0)) = refl
canonicalHaarFeatureReconstruct
  (int8 (+ (suc n))) = refl
canonicalHaarFeatureReconstruct
  (int8 (-[1+ n ])) = refl

canonicalHaarFeatureInjective :
  ∀ {x y} →
  canonicalCReLU8 x ≡ canonicalCReLU8 y →
  x ≡ y
canonicalHaarFeatureInjective {x} {y} eq =
  trans
    (sym (canonicalHaarFeatureReconstruct x))
    (trans
      (cong₂
        (λ a b → int8Sub a b)
        (cong proj₁ eq)
        (cong proj₂ eq))
      (canonicalHaarFeatureReconstruct y))

record HaarFeaturedLinearTransformer : Set where
  constructor haarFeaturedLinearTransformer
  field
    qProjection kProjection vProjection : Int8 → Int8
open HaarFeaturedLinearTransformer public

HaarAccumulator : Set
HaarAccumulator = Int8 × Int8

haarAccumulator-id : HaarAccumulator
haarAccumulator-id = zero8 , zero8

haarAccumulator-op :
  HaarAccumulator → HaarAccumulator → HaarAccumulator
haarAccumulator-op (a₁ , b₁) (a₂ , b₂) =
  int8Add a₁ a₂ , int8Add b₁ b₂

haarAccumulator-op-assoc :
  ∀ x y z →
  haarAccumulator-op
    (haarAccumulator-op x y)
    z
  ≡
  haarAccumulator-op
    x
    (haarAccumulator-op y z)
haarAccumulator-op-assoc
  (a₁ , b₁)
  (a₂ , b₂)
  (a₃ , b₃) =
  cong₂ _,_
    (int8+-assoc a₁ a₂ a₃)
    (int8+-assoc b₁ b₂ b₃)

haarAccumulator-op-idˡ :
  ∀ x →
  haarAccumulator-op haarAccumulator-id x ≡ x
haarAccumulator-op-idˡ (a , b) =
  cong₂ _,_
    (int8+-idˡ a)
    (int8+-idˡ b)

haarAccumulator-op-idʳ :
  ∀ x →
  haarAccumulator-op x haarAccumulator-id ≡ x
haarAccumulator-op-idʳ (a , b) =
  cong₂ _,_
    (int8+-idʳ a)
    (int8+-idʳ b)

haarKeyValueContribution :
  HaarFeaturedLinearTransformer →
  Int8 →
  HaarAccumulator
haarKeyValueContribution T x =
  let (kp , kn) =
        canonicalHaarFeature
          (kProjection T x)
      v = vProjection T x
  in int8Mul kp v , int8Mul kn v

haarAccumulatorStep :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  Int8 →
  HaarAccumulator
haarAccumulatorStep T s x =
  haarAccumulator-op s
    (haarKeyValueContribution T x)

haarQueryRead :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  Int8 →
  Int8
haarQueryRead T (sp , sn) x =
  let (qp , qn) =
        canonicalHaarFeature
          (qProjection T x)
  in int8Add
       (int8Mul qp sp)
       (int8Mul qn sn)

haarLinearTransform :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  List Int8 →
  List Int8
haarLinearTransform T s₀ [] = []
haarLinearTransform T s₀ (x ∷ xs) =
  let s₁ = haarAccumulatorStep T s₀ x
  in haarQueryRead T s₁ x ∷
     haarLinearTransform T s₁ xs

haarLinearTransform-step-law :
  ∀ T s x →
  haarAccumulatorStep T s x ≡
  haarAccumulator-op s
    (haarKeyValueContribution T x)
haarLinearTransform-step-law T s x = refl

haarLinearTransform-associative-prefix :
  ∀ T s x y →
  haarAccumulatorStep T
    (haarAccumulatorStep T s x)
    y
  ≡
  haarAccumulator-op
    (haarAccumulatorStep T s x)
    (haarKeyValueContribution T y)
haarLinearTransform-associative-prefix T s x y = refl

canonicalHaarFeaturedTransformer :
  HaarFeaturedLinearTransformer
canonicalHaarFeaturedTransformer =
  haarFeaturedLinearTransformer
    identityActivation8
    identityActivation8
    identityActivation8

canonicalHaarFeaturedLinearScan :
  HaarAccumulator →
  List Int8 →
  List Int8
canonicalHaarFeaturedLinearScan =
  haarLinearTransform canonicalHaarFeaturedTransformer

