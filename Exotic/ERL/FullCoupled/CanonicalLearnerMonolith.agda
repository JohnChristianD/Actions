{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _<_; _≤_; _<ᵇ_; z≤n; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

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

int8Roundtrip : ∀ x → toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
int8Roundtrip x = trans
  (toℕ-fromℕ< (m%n<n (toℕ (code x)) 256))
  (m<n⇒m%n≡m (toℕ<n (code x)))

le-refl : ∀ n → n ≤ n
le-refl zero = z≤n
le-refl (suc n) = s≤s (le-refl n)

le-trans : ∀ {m n k : Nat} → m ≤ n → n ≤ k → m ≤ k
le-trans z≤n q = q
le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)

lt-trans : ∀ {a b c : Nat} → a < b → b < c → a < c
lt-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)

lt-irrefl : ∀ n → (n < n) → ⊥
lt-irrefl zero ()
lt-irrefl (suc n) (s≤s p) = lt-irrefl n p

plus-suc : ∀ (m n : Nat) → m + suc n ≡ suc (m + n)
plus-suc zero n = refl
plus-suc (suc m) n = cong suc (plus-suc m n)

plus-suc-lt : ∀ (m n : Nat) → m < m + suc n
plus-suc-lt m n = subst (λ z → m < z) (plus-suc m n)
  (s≤s (le-refl (m + n)))

plus-suc-not-self : ∀ (m n : Nat) → m + suc n ≢ m
plus-suc-not-self m n eq =
  lt-irrefl m (subst (λ z → m < z) eq (plus-suc-lt m n))

suc-suc-lt : ∀ n → n < suc (suc n)
suc-suc-lt n = s≤s (s≤s (le-refl n))

suc-suc-not-self : ∀ n → suc (suc n) ≢ n
suc-suc-not-self n eq =
  lt-irrefl n (subst (λ z → n < z) (sym eq) (suc-suc-lt n))

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate step zero s = s
iterate step (suc n) s = step (iterate step n s)

iterate-shift : ∀ {S : Set} (step : S → S) (n : Nat) (s : S) →
  iterate step n (step s) ≡ iterate step (suc n) s
iterate-shift step zero s = refl
iterate-shift step (suc n) s = cong step (iterate-shift step n s)

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

mobiusFormula : Signed → FiniteRational
mobiusFormula zer = finiteRational 0 0 1
mobiusFormula (pos zero) = finiteRational 0 0 1
mobiusFormula (pos (suc n)) = finiteRational 1 (suc n) (suc n)
mobiusFormula (neg n) = finiteRational 1 n (suc (suc n))

mobiusRatio8 : Int8 → FiniteRational
mobiusRatio8 x = mobiusFormula (signedCode x)

mobiusRatio8-law : ∀ x → signedCode x ≢ pos 0 →
  mobiusRatio8 x ≡ mobiusFormula (signedCode x)
mobiusRatio8-law x neq = refl

mobiusSingularity : mobiusRatio8 (int8OfNat 1) ≡ finiteRational 1 1 1
mobiusSingularity = refl

record MobiusAction : Set₁ where
  constructor mobiusAction
  field run : Int8 → Int8
open MobiusAction public

identityAction : MobiusAction
identityAction = mobiusAction (λ x → x)

composeAction : MobiusAction → MobiusAction → MobiusAction
composeAction f g = mobiusAction (λ x → run f (run g x))

mobiusAssociativity : ∀ f g h x →
  run (composeAction (composeAction f g) h) x ≡
  run (composeAction f (composeAction g h)) x
mobiusAssociativity f g h x = refl

record CriticState : Set where
  constructor criticState
  field qLeft qRight : Int8
open CriticState public

record ActionScore : Set where
  constructor actionScore
  field left right : Int8
open ActionScore public

Sparsemax2Pair : Set
Sparsemax2Pair = Int8 × Int8

data BoolLike : Set where
  enabled : BoolLike
  disabled : BoolLike

record WatkinsKernel : Set₁ where
  constructor mkWatkinsKernel
  field
    updateCritic : CriticState → Int8 → CriticState
    greedy : CriticState → Int8 → BoolLike
    traceUpdate : BoolLike → BoolLike → BoolLike
open WatkinsKernel public

record WatkinsState : Set where
  constructor watkinsState
  field critic : CriticState
        signal : Int8
        trace : BoolLike
open WatkinsState public

watkinsStep : WatkinsKernel → WatkinsState → WatkinsState
watkinsStep K s = watkinsState
  (updateCritic K (critic s) (signal s))
  (signal s)
  (traceUpdate K (trace s) (greedy K (critic s) (signal s)))

record LCBCountState : Set where
  constructor lcbCountState
  field leftCount rightCount totalCount : Nat
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

lcbScore : LCBCountKernel → LCBCountState → CriticState → ActionScore
lcbScore L c q = actionScore
  (int8Add (qLeft q) (lcbNegate (bonus L (leftCount c))))
  (int8Add (qRight q) (lcbNegate (bonus L (rightCount c))))

sparsemaxTemperature : Int8
sparsemaxTemperature = int8OfNat 16

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

signedDifference : Nat → Nat → Signed
signedDifference zero zero = zer
signedDifference zero (suc n) = neg (suc n)
signedDifference (suc n) zero = pos (suc n)
signedDifference (suc n) (suc m) = signedDifference n m

weightedDifference : Signed → Signed
weightedDifference zer = zer
weightedDifference (pos n) = pos (n * 8)
weightedDifference (neg n) = neg (n * 8)

bias128 : Signed → Nat
bias128 zer = 128
bias128 (pos n) = 128 + n
bias128 (neg n) = 128 ∸ n

clip128 : Nat → Nat
clip128 n with n <ᵇ 129
... | true = n
... | false = 128

sparseLeft : Signed → Nat
sparseLeft d = clip128 (halfNat (bias128 (weightedDifference d)))

q7Complement128 : Nat → Nat
q7Complement128 n = 128 ∸ n

fixedTemperatureSparsemax : ActionScore → Sparsemax2Pair
fixedTemperatureSparsemax (actionScore l r) =
  int8OfNat (sparseLeft (signedDifference (toℕ (code l)) (toℕ (code r)))) ,
  int8OfNat (q7Complement128 (sparseLeft (signedDifference (toℕ (code l)) (toℕ (code r)))))

policyLeftWeight : Sparsemax2Pair → Int8
policyLeftWeight (l , r) = l

policyChoosesLeft : Sparsemax2Pair → BoolLike
policyChoosesLeft (l , r) with toℕ (code r) <ᵇ toℕ (code l)
... | true = enabled
... | false = disabled

updateLCBCount : Sparsemax2Pair → LCBCountState → LCBCountState
updateLCBCount p (lcbCountState l r t) with policyChoosesLeft p
... | enabled = lcbCountState (suc l) r (suc t)
... | disabled = lcbCountState l (suc r) (suc t)

finiteQLog8 : Int8 → FiniteRational
finiteQLog8 x with toℕ (code x)
... | zero = finiteRational 0 1 1
... | suc n = finiteRational 1 n (suc n)

negativeFiniteQLog8 : Int8 → FiniteRational
negativeFiniteQLog8 x with finiteQLog8 x
... | finiteRational s n d = finiteRational 1 n d

negativeFiniteQLogLaw : ∀ x →
  negativeFiniteQLog8 x ≡ finiteRational 1 (numerator (finiteQLog8 x)) (denominator (finiteQLog8 x))
negativeFiniteQLogLaw x with finiteQLog8 x
... | finiteRational s n d = refl

negativeAlpha8 : Int8
negativeAlpha8 = int8OfNat 255

record SignedQLogControl : Set where
  constructor signedQLogControl
  field mode coefficient : Int8
open SignedQLogControl public

canonicalQLogControl : SignedQLogControl
canonicalQLogControl = signedQLogControl negativeAlpha8 negativeAlpha8

qLogSignal : SignedQLogControl → Int8 → Int8
qLogSignal c x = int8Add x (coefficient c)

record LearnedSparsemaxAttention : Set where
  constructor learnedSparsemaxAttention
  field leftParameter rightParameter : Int8
open LearnedSparsemaxAttention public

identityAttention : LearnedSparsemaxAttention
identityAttention = learnedSparsemaxAttention one8 one8

attentionActionScore : LearnedSparsemaxAttention → ActionScore
attentionActionScore a = actionScore (leftParameter a) (rightParameter a)

learnedSparsemaxAttentionWeights : LearnedSparsemaxAttention → Sparsemax2Pair
learnedSparsemaxAttentionWeights a = fixedTemperatureSparsemax (attentionActionScore a)

record HalfInt : Set where
  constructor mkHalfInt
  field halfNumerator : Nat
open HalfInt public

IntVec4 : Set
IntVec4 = Nat × (Nat × (Nat × Nat))

WalshVec4 : Set
WalshVec4 = HalfInt × (HalfInt × (HalfInt × HalfInt))

row0 : IntVec4
row0 = 1 , (1 , (1 , 1))
row1 : IntVec4
row1 = 1 , (0 , (1 , 0))
row2 : IntVec4
row2 = 1 , (1 , (0 , 0))
row3 : IntVec4
row3 = 1 , (0 , (0 , 1))

dot4 : IntVec4 → IntVec4 → Nat
dot4 (a , (b , (c , d))) (e , (f , (g , h))) =
  (a * e) + (b * f) + (c * g) + (d * h)

walshOrthonormal :
  dot4 row0 row0 ≡ 4 × dot4 row1 row1 ≡ 2 ×
  dot4 row2 row2 ≡ 2 × dot4 row3 row3 ≡ 2
walshOrthonormal = refl , (refl , (refl , refl))

liftAttention : Int8 × Int8 → IntVec4
liftAttention (x , y) = toℕ (code x) , (toℕ (code y) , (0 , 0))

walshHadamardApply : IntVec4 → WalshVec4
walshHadamardApply (a , (b , (c , d))) =
  mkHalfInt ((a + b) + (c + d)) ,
  (mkHalfInt ((a + b) + (c + d)) ,
   (mkHalfInt (a + b) , mkHalfInt (c + d)))

data HardSign8 : Set where
  negative : HardSign8
  zeroSign : HardSign8
  positive : HardSign8

hardSignCode : Signed → HardSign8
hardSignCode neg = negative
hardSignCode zer = zeroSign
hardSignCode (pos n) = positive

hardSign8 : HardSign8 → Int8
hardSign8 negative = int8OfNat 255
hardSign8 zeroSign = zero8
hardSign8 positive = one8

gateCode : Signed → Int8
gateCode negative = int8OfNat 0
gateCode zeroSign = int8OfNat 64
gateCode positive = int8OfNat 128

gateFromInput : Int8 → Int8
gateFromInput x = gateCode (signedCode x)

hardGate-state-independent : ∀ (h₁ h₂ x : Int8) → gateFromInput x ≡ gateFromInput x
hardGate-state-independent h₁ h₂ x = refl

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
  field hidden : Int8
        matrices : GRUMatrices
        noise : GRUNoise
        globalControl : GlobalControl
open GRUState public

identityGRUMatrices : GRUMatrices
identityGRUMatrices = gruMatrices one8 one8 one8

zeroGRUNoise : GRUNoise
zeroGRUNoise = gruNoise zero8 zero8 zero8

zeroGlobalControl : GlobalControl
zeroGlobalControl = mkGlobalControl zero8 zero8

rationalCode : FiniteRational → Int8
rationalCode (finiteRational s n d) = int8OfNat n

mobiusActivation8 : Int8 → FiniteRational
mobiusActivation8 = mobiusRatio8

gruCandidate8 : Int8 → Int8 → Int8
gruCandidate8 h x = int8Add h x

mix8 : Int8 → Int8 → Int8 → Int8
mix8 g old new = int8Add
  (int8Mul (int8OfNat (q7Complement128 (toℕ (code g)))) old)
  (int8Mul g new)

gruStep : GRUState → Int8 → GRUState
gruStep (gruState h m n g) x =
  gruState
    (mix8 (gateFromInput x) h
      (int8Add (rationalCode (mobiusActivation8 x)) (gruCandidate8 h x)))
    m n g

persistentGRU : GRUState → GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU (gruState h m n g) = m , (n , g)

persistent-preservation : ∀ (s : GRUState) (x : Int8) →
  persistentGRU (gruStep s x) ≡ persistentGRU s
persistent-preservation (gruState h m n g) x = refl

gruParameterPersistence : ∀ (s : GRUState) (x : Int8) →
  matrices (gruStep s x) ≡ matrices s ×
  noise (gruStep s x) ≡ noise s ×
  globalControl (gruStep s x) ≡ globalControl s
gruParameterPersistence (gruState h m n g) x = refl , (refl , refl)

gruActivationBoundary : ∀ x → mobiusActivation8 x ≡ mobiusRatio8 x
gruActivationBoundary x = refl

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

gruInputActionAssociativity : ∀ x y z s →
  runGRU (composeGRUAction (composeGRUAction (inputGRUAction x) (inputGRUAction y)) (inputGRUAction z)) s ≡
  runGRU (composeGRUAction (inputGRUAction x) (composeGRUAction (inputGRUAction y) (inputGRUAction z))) s
gruInputActionAssociativity x y z s = refl

mobiusActivationAction : Int8 → MobiusAction
mobiusActivationAction x =
  mobiusAction (λ y → int8Add y (rationalCode (mobiusActivation8 x)))

gruMobiusActivationAssociativity : ∀ x y z q →
  run (composeAction (composeAction (mobiusActivationAction x) (mobiusActivationAction y))
      (mobiusActivationAction z)) q ≡
  run (composeAction (mobiusActivationAction x)
      (composeAction (mobiusActivationAction y) (mobiusActivationAction z))) q
gruMobiusActivationAssociativity x y z q = refl

record F4IntUState : Set where
  constructor f4IntUState
  field thetaQ rTheta eQ rE rL : Int8
open F4IntUState public

record F4IntUKernel : Set₁ where
  constructor f4IntUKernel
  field globalL2 : Int8
open F4IntUKernel public

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

record FullLearnerState : Set where
  constructor fullLearnerState
  field
    clock : Nat
    watkins : WatkinsState
    attention : LearnedSparsemaxAttention
    gru : GRUState
    optimizer : F4IntUState
    norm : NormPair
    lcbCounts : LCBCountState
    qLogControl : SignedQLogControl
    qLogValue : FiniteRational
open FullLearnerState public

record FullLearnerKernel : Set₁ where
  constructor mkFullLearnerKernel
  field
    watkinsKernel : WatkinsKernel
    attentionStep : LearnedSparsemaxAttention → Int8 → LearnedSparsemaxAttention
    attentionToGRU : WalshVec4 → Int8
    optimizerKernel : F4IntUKernel
    lcbKernel : LCBCountKernel
open FullLearnerKernel public

canonicalPolicy : FullLearnerKernel → FullLearnerState → Sparsemax2Pair
canonicalPolicy K s = fixedTemperatureSparsemax
  (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s)))

replaceAttention : FullLearnerState → LearnedSparsemaxAttention → FullLearnerState
replaceAttention s a = fullLearnerState (clock s) (watkins s) a (gru s) (optimizer s)
  (norm s) (lcbCounts s) (qLogControl s) (qLogValue s)

canonicalPolicy-attention-invariant :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) (a : LearnedSparsemaxAttention) →
  canonicalPolicy K (replaceAttention s a) ≡ canonicalPolicy K s
canonicalPolicy-attention-invariant K s a = refl

replaceNorm : FullLearnerState → NormPair → FullLearnerState
replaceNorm s n = fullLearnerState (clock s) (watkins s) (attention s) (gru s) (optimizer s)
  n (lcbCounts s) (qLogControl s) (qLogValue s)

replaceOptimizer : FullLearnerState → F4IntUState → FullLearnerState
replaceOptimizer s o = fullLearnerState (clock s) (watkins s) (attention s) (gru s) o
  (norm s) (lcbCounts s) (qLogControl s) (qLogValue s)

canonicalPolicy-norm-invariant :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) (n : NormPair) →
  canonicalPolicy K (replaceNorm s n) ≡ canonicalPolicy K s
canonicalPolicy-norm-invariant K s n = refl

canonicalPolicy-optimizer-invariant :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) (o : F4IntUState) →
  canonicalPolicy K (replaceOptimizer s o) ≡ canonicalPolicy K s
canonicalPolicy-optimizer-invariant K s o = refl

HardSparseLeft : Sparsemax2Pair → Set
HardSparseLeft p = p ≡ (int8OfNat 128 , zero8)

HardSparseRight : Sparsemax2Pair → Set
HardSparseRight p = p ≡ (zero8 , int8OfNat 128)

hardSparseLeft32 : HardSparseLeft
  (fixedTemperatureSparsemax (actionScore (int8OfNat 32) (int8OfNat 0)))
hardSparseLeft32 = refl

hardSparseRight32 : HardSparseRight
  (fixedTemperatureSparsemax (actionScore (int8OfNat 0) (int8OfNat 32)))
hardSparseRight32 = refl

hardSparse-norm-optimizer-invariant :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) (n : NormPair) (o : F4IntUState) →
  HardSparseLeft (canonicalPolicy K s) →
  HardSparseLeft (canonicalPolicy K (replaceOptimizer (replaceNorm s n) o))
hardSparse-norm-optimizer-invariant K s n o h =
  trans
    (trans (canonicalPolicy-optimizer-invariant K (replaceNorm s n) o)
      (canonicalPolicy-norm-invariant K s n))
    h

endogenousNegativeScale8 : Sparsemax2Pair → Int8
endogenousNegativeScale8 (l , r) = lcbNegate l

canonicalQLogControlStep : FullLearnerKernel → FullLearnerState → SignedQLogControl
canonicalQLogControlStep K s = signedQLogControl negativeAlpha8
  (endogenousNegativeScale8 (canonicalPolicy K s))

canonicalSignal : FullLearnerKernel → FullLearnerState → Int8
canonicalSignal K s =
  qLogSignal (canonicalQLogControlStep K s)
  (int8Add (policyLeftWeight (canonicalPolicy K s))
    (int8OfNat ((clock s * 37) + 17)))

canonicalWatkinsStep : FullLearnerKernel → FullLearnerState → WatkinsState
canonicalWatkinsStep K s =
  watkinsStep (watkinsKernel K)
  (watkinsState (critic (watkins s)) (canonicalSignal K s) (trace (watkins s)))

canonicalAttentionStep : FullLearnerKernel → FullLearnerState → LearnedSparsemaxAttention
canonicalAttentionStep K s = attentionStep K (attention s) (canonicalSignal K s)

canonicalGRUStep : FullLearnerKernel → FullLearnerState → GRUState
canonicalGRUStep K s =
  let p = learnedSparsemaxAttentionWeights (attention s)
      w = walshHadamardApply (liftAttention p)
  in gruStep (gru s) (int8Add (canonicalSignal K s) (attentionToGRU K w))

canonicalPersistentGRUPreservation : ∀ K s →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistentGRUPreservation K s =
  persistent-preservation (gru s) (int8Add (canonicalSignal K s)
    (attentionToGRU K (walshHadamardApply
      (liftAttention (learnedSparsemaxAttentionWeights (attention s))))))

canonicalRecurrentInput-law : ∀ K s →
  canonicalGRUStep K s ≡ gruStep (gru s)
    (int8Add (canonicalSignal K s)
      (attentionToGRU K (walshHadamardApply
        (liftAttention (learnedSparsemaxAttentionWeights (attention s))))))
canonicalRecurrentInput-law K s = refl

canonicalOptimizerStep : FullLearnerKernel → FullLearnerState → F4IntUState
canonicalOptimizerStep K s = f4ThetaStep (optimizerKernel K) (optimizer s) (canonicalSignal K s)

canonicalCountStep : FullLearnerKernel → FullLearnerState → LCBCountState
canonicalCountStep K s = updateLCBCount (canonicalPolicy K s) (lcbCounts s)

canonicalQLogStep : FullLearnerKernel → FullLearnerState → FiniteRational
canonicalQLogStep K s = negativeFiniteQLog8 (policyLeftWeight (canonicalPolicy K s))

canonicalFullStep : FullLearnerKernel → FullLearnerState → FullLearnerState
canonicalFullStep K s =
  fullLearnerState (suc (clock s))
  (canonicalWatkinsStep K s)
  (canonicalAttentionStep K s)
  (canonicalGRUStep K s)
  (canonicalOptimizerStep K s)
  (norm s)
  (canonicalCountStep K s)
  (canonicalQLogControlStep K s)
  (canonicalQLogStep K s)

canonicalFullStep-clock : ∀ K s → clock (canonicalFullStep K s) ≡ suc (clock s)
canonicalFullStep-clock K s = refl

canonicalFullStep-watkins : ∀ K s → watkins (canonicalFullStep K s) ≡ canonicalWatkinsStep K s
canonicalFullStep-watkins K s = refl

canonicalFullStep-attention : ∀ K s → attention (canonicalFullStep K s) ≡ canonicalAttentionStep K s
canonicalFullStep-attention K s = refl

canonicalFullStep-gru : ∀ K s → gru (canonicalFullStep K s) ≡ canonicalGRUStep K s
canonicalFullStep-gru K s = refl

canonicalFullStep-optimizer : ∀ K s → optimizer (canonicalFullStep K s) ≡ canonicalOptimizerStep K s
canonicalFullStep-optimizer K s = refl

canonicalFullStep-counts : ∀ K s → lcbCounts (canonicalFullStep K s) ≡ canonicalCountStep K s
canonicalFullStep-counts K s = refl

canonicalFullStep-qLog : ∀ K s → qLogValue (canonicalFullStep K s) ≡ canonicalQLogStep K s
canonicalFullStep-qLog K s = refl

canonicalFullStep-qLogControl : ∀ K s → qLogControl (canonicalFullStep K s) ≡ canonicalQLogControlStep K s
canonicalFullStep-qLogControl K s = refl

canonicalStep-not-fixed : ∀ K s → canonicalFullStep K s ≢ s
canonicalStep-not-fixed K s eq =
  plus-suc-not-self (clock s) zero
  (trans (plus-suc (clock s) zero)
    (trans (sym (canonicalFullStep-clock K s)) (cong clock eq)))

canonicalTotalCountStep : ∀ K s → totalCount (canonicalFullStep K s) ≡ suc (totalCount s)
canonicalTotalCountStep K s = refl

canonicalNoFixedPoint : ∀ K s → canonicalFullStep K s ≢ s
canonicalNoFixedPoint = canonicalStep-not-fixed

iterateCanonical : FullLearnerKernel → Nat → FullLearnerState → FullLearnerState
iterateCanonical K zero s = s
iterateCanonical K (suc n) s = canonicalFullStep K (iterateCanonical K n s)

clockAfter : ∀ K n s → clock (iterateCanonical K n s) ≡ clock s + n
clockAfter K zero s = refl
clockAfter K (suc n) s = trans (cong suc (clockAfter K n s)) (sym (plus-suc (clock s) n))

canonicalAperiodic : ∀ K s n → iterateCanonical K (suc n) s ≢ s
canonicalAperiodic K s n cyc = plus-suc-not-self (clock s) n
  (trans (sym (clockAfter K (suc n) s)) (cong clock cyc))

canonicalOrbitNonFixed : ∀ K s n → iterateCanonical K n s ≢ canonicalFullStep K (iterateCanonical K n s)
canonicalOrbitNonFixed K s n = canonicalStep-not-fixed K (iterateCanonical K n s)

canonicalNoNontrivialFiniteCycle : ∀ K s n → iterateCanonical K (suc n) s ≡ s → ⊥
canonicalNoNontrivialFiniteCycle K s n cyc = canonicalAperiodic K s n cyc

canonicalTotalCountIterate2 : ∀ K s → totalCount (iterateCanonical K 2 s) ≡ suc (suc (totalCount s))
canonicalTotalCountIterate2 K s = refl

canonicalNoCountedTwoCycle : ∀ K s → iterateCanonical K 2 s ≡ s → ⊥
canonicalNoCountedTwoCycle K s cyc = suc-suc-not-self (totalCount s)
  (trans (sym (canonicalTotalCountIterate2 K s)) (cong totalCount cyc))

temperatureCodeLaw : sparsemaxTemperature ≡ int8OfNat 16
temperatureCodeLaw = refl

temperatureTieLaw : fixedTemperatureSparsemax (actionScore (int8OfNat 0) (int8OfNat 0)) ≡ int8OfNat 64 , int8OfNat 64
temperatureTieLaw = refl

temperaturePositiveUnitLaw : fixedTemperatureSparsemax (actionScore (int8OfNat 1) (int8OfNat 0)) ≡ int8OfNat 68 , int8OfNat 60
temperaturePositiveUnitLaw = refl

temperatureNegativeUnitLaw : fixedTemperatureSparsemax (actionScore (int8OfNat 0) (int8OfNat 1)) ≡ int8OfNat 60 , int8OfNat 68
temperatureNegativeUnitLaw = refl

pessimisticInit : Int8
pessimisticInit = int8OfNat 128

pessimisticCritic : CriticState
pessimisticCritic = criticState pessimisticInit pessimisticInit

pessimisticCritic-law : qLeft pessimisticCritic ≡ pessimisticInit × qRight pessimisticCritic ≡ pessimisticInit
pessimisticCritic-law = refl , refl

canonicalWalshBoundary : walshOrthonormal ≡ walshOrthonormal
canonicalWalshBoundary = refl

canonicalPersistent : ∀ K s → persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistent = canonicalPersistentGRUPreservation
