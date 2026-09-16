{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith where

open import Agda.Builtin.Equality using (_≡_; _≢_; refl; sym; cong; subst; trans)
import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Entire learner kernel. No environment or statistical carrier occurs here.
------------------------------------------------------------------------

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

int8Mul : Int8 → Int8 → Int8
int8Mul x y = int8OfNat (toℕ (code x) * toℕ (code y))

int8Roundtrip : ∀ x → toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
int8Roundtrip x = trans
  (toℕ-fromℕ< (m%n<n (toℕ (code x)) 256))
  (m<n⇒m%n≡m (toℕ<n (code x)))

------------------------------------------------------------------------
-- Nat deductions used by contradiction theorems.
------------------------------------------------------------------------

lt-trans : ∀ {a b c : Nat} → a < b → b < c → a < c
lt-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)
  where
  le-trans : ∀ {m n k : Nat} → m ≤ n → n ≤ k → m ≤ k
  le-trans z≤n q = q
  le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)

lt-irrefl : ∀ n → ¬ (n < n)
lt-irrefl zero ()
lt-irrefl (suc n) (s≤s p) = lt-irrefl n p

le-refl : ∀ n → n ≤ n
le-refl zero = z≤n
le-refl (suc n) = s≤s (le-refl n)

le-trans : ∀ {m n k : Nat} → m ≤ n → n ≤ k → m ≤ k
le-trans z≤n q = q
le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)

plus-suc : ∀ (m n : Nat) → m + suc n ≡ suc (m + n)
plus-suc zero n = refl
plus-suc (suc m) n = cong suc (plus-suc m n)

suc-injective : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

plus-suc-not-self : ∀ (r n : Nat) → r + suc n ≢ r
plus-suc-not-self zero n = λ ()
plus-suc-not-self (suc r) n eq =
  plus-suc-not-self r n (suc-injective eq')
  where
  eq' : suc r ≡ suc r
  eq' = trans (sym (plus-suc r n)) (trans eq (plus-suc r n))

suc-suc-not-self : ∀ n → suc (suc n) ≢ n
suc-suc-not-self zero ()
suc-suc-not-self (suc n) eq = suc-suc-not-self n (suc-injective eq)

------------------------------------------------------------------------
-- Exact finite iteration.
------------------------------------------------------------------------

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate step zero s = s
iterate step (suc n) s = step (iterate step n s)

iterate-shift :
  ∀ {S : Set} (step : S → S) (n : Nat) (s : S) →
  iterate step n (step s) ≡ iterate step (suc n) s
iterate-shift step zero s = refl
iterate-shift step (suc n) s = cong step (iterate-shift step n s)

OrbitNonFixed : ∀ {S : Set} {step : S → S} → S → Set
OrbitNonFixed {step = step} s = ∀ n → iterate step n s ≢ step (iterate step n s)

------------------------------------------------------------------------
-- Exact finite-rational Mobius boundary x / (1 - x).
------------------------------------------------------------------------

record FiniteRational : Set where
  constructor finiteRational
  field numerator denominator : I.Int
open FiniteRational public

negInt : I.Int → I.Int
negInt (I.pos zero) = I.pos zero
negInt (I.pos (suc n)) = I.negsuc n
negInt (I.negsuc n) = I.pos (suc n)

signedCode : Int8 → I.Int
signedCode x with toℕ (code x) <ᵇ 128
... | true = I.pos (toℕ (code x))
... | false = I.negsuc (255 ∸ toℕ (code x))

mobiusRatio8 : Int8 → FiniteRational
mobiusRatio8 x with signedCode x
... | I.pos zero = finiteRational (I.pos 0) (I.pos 1)
... | I.pos (suc zero) = finiteRational (I.pos 0) (I.pos 1)
... | I.pos (suc (suc n)) = finiteRational (I.pos (suc (suc n))) (I.negsuc n)
... | I.negsuc n = finiteRational (I.negsuc n) (I.pos (suc (suc n)))

mobiusRatio8-law : ∀ x → signedCode x ≢ I.pos 1 →
  mobiusRatio8 x ≡ finiteRational (signedCode x) (I._-_ (I.pos 1) (signedCode x))
mobiusRatio8-law x neq with signedCode x
... | I.pos zero = refl
... | I.pos (suc zero) = λ q → neq q
... | I.pos (suc (suc n)) = refl
... | I.negsuc n = refl

mobiusSingularity : mobiusRatio8 (int8OfNat 1) ≡ finiteRational (I.pos 0) (I.pos 1)
mobiusSingularity = refl

record MobiusAction : Set₁ where
  constructor mobiusAction
  field run : Int8 → Int8
open MobiusAction public

identityAction : MobiusAction
identityAction = mobiusAction (λ x → x)

composeAction : MobiusAction → MobiusAction → MobiusAction
composeAction f g = mobiusAction (λ x → run f (run g x))

mobiusAssociativity :
  ∀ f g h x →
  run (composeAction (composeAction f g) h) x ≡
  run (composeAction f (composeAction g h)) x
mobiusAssociativity f g h x = refl

------------------------------------------------------------------------
-- Watkins critic-only policy source, sparsemax temperature, LCB memory.
------------------------------------------------------------------------

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
enabled disabled : BoolLike

record WatkinsKernel : Set₁ where
  constructor watkinsKernel
  field updateCritic : CriticState → Int8 → CriticState
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

halfSigned : I.Int → I.Int
halfSigned (I.pos n) = I.pos (halfNat n)
halfSigned (I.negsuc n) = I.pos zero

q7Clamp : I.Int → Int8
q7Clamp (I.pos n) with n <ᵇ 129
... | true = int8OfNat n
... | false = int8OfNat 128
q7Clamp (I.negsuc n) = zero8

q7Complement128 : Int8 → Int8
q7Complement128 x = int8OfNat (128 ∸ toℕ (code x))

fixedTemperatureSparsemax : ActionScore → Sparsemax2Pair
fixedTemperatureSparsemax (actionScore l r) =
  let d = I._-_ (signedCode l) (signedCode r)
      leftWeight = q7Clamp (halfSigned (I._+_ (I.pos 128) (I._*_ (I.pos 8) d)))
  in leftWeight , q7Complement128 leftWeight

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

------------------------------------------------------------------------
-- Negative Munchausen-style finite q-log shaping.
------------------------------------------------------------------------

finiteQLog8 : Int8 → FiniteRational
finiteQLog8 x with toℕ (code x)
... | zero = finiteRational (I.pos 1) (I.pos 1)
... | suc n = finiteRational (I.pos n) (I.pos (suc n))

negativeFiniteQLog8 : Int8 → FiniteRational
negativeFiniteQLog8 x =
  let q = finiteQLog8 x
  in finiteRational (negInt (numerator q)) (denominator q)

negativeFiniteQLogLaw : ∀ x →
  negativeFiniteQLog8 x ≡ finiteRational (negInt (numerator (finiteQLog8 x))) (denominator (finiteQLog8 x))
negativeFiniteQLogLaw x = refl

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

------------------------------------------------------------------------
-- Learned sparsemax attention stays learner-internal and actor-free.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Exact H4 / 2 Walsh boundary.
------------------------------------------------------------------------

record HalfInt : Set where
  constructor mkHalfInt
  field numerator : I.Int
open HalfInt public

IntVec4 : Set
IntVec4 = I.Int × (I.Int × (I.Int × I.Int))

WalshVec4 : Set
WalshVec4 = HalfInt × (HalfInt × (HalfInt × HalfInt))

row0 : IntVec4
row0 = I.pos 1 , (I.pos 1 , (I.pos 1 , I.pos 1))
row1 : IntVec4
row1 = I.pos 1 , (I.negsuc 0 , (I.pos 1 , I.negsuc 0))
row2 : IntVec4
row2 = I.pos 1 , (I.pos 1 , (I.negsuc 0 , I.negsuc 0))
row3 : IntVec4
row3 = I.pos 1 , (I.negsuc 0 , (I.negsuc 0 , I.pos 1))

dot4 : IntVec4 → IntVec4 → I.Int
dot4 (a , (b , (c , d))) (e , (f , (g , h))) =
  I._+_ (I._+_ (I._*_ a e) (I._*_ b f)) (I._+_ (I._*_ c g) (I._*_ d h))

walshOrthonormal :
  dot4 row0 row0 ≡ I.pos 4 × dot4 row1 row1 ≡ I.pos 4 ×
  dot4 row2 row2 ≡ I.pos 4 × dot4 row3 row3 ≡ I.pos 4 ×
  dot4 row0 row1 ≡ I.pos 0 × dot4 row0 row2 ≡ I.pos 0 ×
  dot4 row0 row3 ≡ I.pos 0 × dot4 row1 row2 ≡ I.pos 0 ×
  dot4 row1 row3 ≡ I.pos 0 × dot4 row2 row3 ≡ I.pos 0
walshOrthonormal = refl , (refl , (refl , (refl , (refl , (refl , (refl , (refl , (refl , refl))))))))

liftAttention : Int8 × Int8 → IntVec4
liftAttention (x , y) =
  I.pos (toℕ (code x)) , (I.pos (toℕ (code y)) , (I.pos 0 , I.pos 0))

walshHadamardApply : IntVec4 → WalshVec4
walshHadamardApply (a , (b , (c , d))) =
  mkHalfInt (I._+_ (I._+_ a b) (I._+_ c d)) ,
  (mkHalfInt (I._+_ (I._-_ a b) (I._-_ c d)) ,
    (mkHalfInt (I._+_ (I._+_ a b) (I._+_ (I.negsuc 0) (I._+_ c d))) ,
      mkHalfInt (I._+_ (I._-_ a b) (I._+_ (I._*_ (I.negsuc 0) c) d))))

------------------------------------------------------------------------
-- Hard-sign gate + persistent, input-driven finite-rational GRU.
------------------------------------------------------------------------

data HardSign8 : Set where
  negative zeroSign positive : HardSign8

hardSignCode : I.Int → HardSign8
hardSignCode (I.pos zero) = zeroSign
hardSignCode (I.pos (suc n)) = positive
hardSignCode (I.negsuc n) = negative

hardSign8 : HardSign8 → Int8
hardSign8 negative = int8OfNat 255
hardSign8 zeroSign = zero8
hardSign8 positive = one8

gateCode : I.Int → Int8
gateCode z with hardSignCode z
... | negative = int8OfNat 0
... | zeroSign = int8OfNat 64
... | positive = int8OfNat 128

gateComplement : Int8 → Int8
gateComplement g = int8OfNat (128 ∸ toℕ (code g))

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
  constructor globalControl
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
zeroGlobalControl = globalControl zero8 zero8

code8FromRational : FiniteRational → Int8
code8FromRational q = int8OfNat (signedNatural (numerator q))
  where
  signedNatural : I.Int → Nat
  signedNatural (I.pos n) = n
  signedNatural (I.negsuc n) = zero

mobiusActivation8 : Int8 → FiniteRational
mobiusActivation8 = mobiusRatio8

gruCandidate8 : Int8 → Int8 → Int8
gruCandidate8 h x = int8Add h x

mix8 : Int8 → Int8 → Int8 → Int8
mix8 g old new = int8Add (int8Mul (gateComplement g) old) (int8Mul g new)

gruStep : GRUState → Int8 → GRUState
gruStep (gruState h m n g) x =
  gruState
    (mix8 (gateFromInput x) h
      (int8Add (code8FromRational (mobiusActivation8 x)) (gruCandidate8 h x)))
    m n g

persistentGRU : GRUState → GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU (gruState h m n g) = m , (n , g)

persistent-preservation :
  ∀ (s : GRUState) (x : Int8) → persistentGRU (gruStep s x) ≡ persistentGRU s
persistent-preservation (gruState h m n g) x = refl

gruParameterPersistence :
  ∀ (s : GRUState) (x : Int8) →
  matrices (gruStep s x) ≡ matrices s ×
  noise (gruStep s x) ≡ noise s ×
  globalControl (gruStep s x) ≡ globalControl s
gruParameterPersistence (gruState h m n g) x = refl , (refl , refl)

gruActivationBoundary : ∀ x → mobiusActivation8 x ≡ mobiusRatio8 x
gruActivationBoundary x = refl

------------------------------------------------------------------------
-- Global F4-Int-U(p)-style optimizer with explicit global L2 correction.
------------------------------------------------------------------------

record F4IntUState : Set where
  constructor f4IntUState
  field thetaQ rTheta eQ rE rL : Int8
open F4IntUState public

record F4IntUKernel : Set where
  constructor f4IntUKernel
  field globalL2 : Int8
open F4IntUKernel public

l2Correction : Int8 → Int8
l2Correction x = int8OfNat (256 ∸ toℕ (code x))

f4ThetaStep : F4IntUKernel → F4IntUState → Int8 → F4IntUState
f4ThetaStep K s g =
  let raw = int8Add (int8Add (thetaQ s) g) (l2Correction (globalL2 K))
  in f4IntUState raw zero8 (eQ s) (rE s) (rL s)

f4ParameterInvariant : ∀ (K : F4IntUKernel) (s : F4IntUState) (g : Int8) →
  thetaQ (f4ThetaStep K s g) ≡ int8Add (int8Add (thetaQ s) g) (l2Correction (globalL2 K))
f4ParameterInvariant K s g = refl

record NormPair : Set where
  constructor normPair
  field l1 path : Int8
open NormPair public

------------------------------------------------------------------------
-- Complete learner state and deterministic endogenous one-step map.
------------------------------------------------------------------------

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
  constructor fullLearnerKernel
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

endogenousNegativeScale8 : Sparsemax2Pair → Int8
endogenousNegativeScale8 (l , r) = l2Correction l

canonicalQLogControlStep : FullLearnerKernel → FullLearnerState → SignedQLogControl
canonicalQLogControlStep K s =
  signedQLogControl negativeAlpha8 (endogenousNegativeScale8 (canonicalPolicy K s))

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
  let policyRepresentation = learnedSparsemaxAttentionWeights (attention s)
      transformed = walshHadamardApply (liftAttention policyRepresentation)
      extra = attentionToGRU K transformed
  in gruStep (gru s) (int8Add (canonicalSignal K s) extra)

canonicalPersistentGRUPreservation :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistentGRUPreservation K s =
  persistent-preservation (gru s)
    (int8Add (canonicalSignal K s)
      (attentionToGRU K
        (walshHadamardApply
          (liftAttention (learnedSparsemaxAttentionWeights (attention s))))))

canonicalRecurrentInput-law :
  ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  canonicalGRUStep K s ≡
  gruStep (gru s)
    (int8Add (canonicalSignal K s)
      (attentionToGRU K
        (walshHadamardApply
          (liftAttention (learnedSparsemaxAttentionWeights (attention s))))))
canonicalRecurrentInput-law K s = refl

canonicalOptimizerStep : FullLearnerKernel → FullLearnerState → F4IntUState
canonicalOptimizerStep K s =
  f4ThetaStep (optimizerKernel K) (optimizer s) (canonicalSignal K s)

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
    (trans
      (plus-suc (clock s) zero)
      (trans
        (sym (canonicalFullStep-clock K s))
        (cong clock eq)))

canonicalTotalCountStep : ∀ K s → totalCount (canonicalFullStep K s) ≡ suc (totalCount s)
canonicalTotalCountStep K s = refl

canonicalNoFixedPoint : ∀ K s → canonicalFullStep K s ≢ s
canonicalNoFixedPoint = canonicalStep-not-fixed

iterateCanonical : FullLearnerKernel → Nat → FullLearnerState → FullLearnerState
iterateCanonical K zero s = s
iterateCanonical K (suc n) s = canonicalFullStep K (iterateCanonical K n s)

clockAfter : ∀ K n s → clock (iterateCanonical K n s) ≡ clock s + n
clockAfter K zero s = refl
clockAfter K (suc n) s =
  trans (cong suc (clockAfter K n s)) (sym (plus-suc (clock s) n))

canonicalAperiodic : ∀ K s n → iterateCanonical K (suc n) s ≢ s
canonicalAperiodic K s n cyc =
  plus-suc-not-self (clock s) n
    (trans
      (sym (clockAfter K (suc n) s))
      (cong clock cyc))

canonicalOrbitNonFixed : ∀ K s n → iterateCanonical K n s ≢ canonicalFullStep K (iterateCanonical K n s)
canonicalOrbitNonFixed K s n = canonicalStep-not-fixed K (iterateCanonical K n s)

canonicalNoNontrivialFiniteCycle : ∀ K s n →
  iterateCanonical K (suc n) s ≡ s → ⊥
canonicalNoNontrivialFiniteCycle K s n cyc = canonicalAperiodic K s n cyc

canonicalNoCountedTwoCycle : ∀ K s →
  iterateCanonical K 2 s ≡ s → ⊥
canonicalNoCountedTwoCycle K s cyc =
  suc-suc-not-self (totalCount (iterateCanonical K 0 s))
    (trans
      (sym (cong suc (canonicalTotalCountStep K s)))
      (trans
        (sym (canonicalTotalCountStep K (canonicalFullStep K s)))
        (cong totalCount cyc)))

------------------------------------------------------------------------
-- Concrete regression laws.
------------------------------------------------------------------------

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

canonicalPersistent : ∀ (K : FullLearnerKernel) (s : FullLearnerState) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistent = canonicalPersistentGRUPreservation
