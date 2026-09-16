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
  negativeFiniteQLog8 x ≡ negativeFiniteQLog8 x
negativeFiniteQLogLaw x = refl

record LearnedSparsemaxAttention : Set where
  constructor learnedSparsemaxAttention
  field leftKey rightKey : Int8
open LearnedSparsemaxAttention public

learnedSparsemaxAttention : Sparsemax2Pair → LearnedSparsemaxAttention
learnedSparsemaxAttention p = learnedSparsemaxAttention (policyLeftWeight p) (snd p)

canonicalAttentionStep : FullLearnerKernel → FullLearnerState → LearnedSparsemaxAttention
canonicalAttentionStep K s = learnedSparsemaxAttention (fixedTemperatureSparsemax (canonicalQScores K s))

record GRUState : Set where
  constructor gruState
  field
    hiddenState : Int8
    gruInputMatrix gruRecurrentMatrix gruBias : Int8
    noiseUpdate noiseReset noiseCandidate : Int8
    globalControlL2 globalControlF4 : Int8
open GRUState public

persistentGRU : GRUState →
  Int8 × Int8 × Int8 × Int8 × Int8 × Int8 × Int8 × Int8
persistentGRU s =
  hiddenState s , gruInputMatrix s , gruRecurrentMatrix s , gruBias s ,
  noiseUpdate s , noiseReset s , noiseCandidate s , globalControlL2 s

gruStep : FullLearnerKernel → GRUState → LearnedSparsemaxAttention → GRUState
gruStep K g a = gruState
  (int8Add (hiddenState g) (leftKey a))
  (int8Add (gruInputMatrix g) (rightKey a))
  (int8Add (gruRecurrentMatrix g) (rightKey a))
  (int8Add (gruBias g) (leftKey a))
  (noiseUpdate g)
  (noiseReset g)
  (noiseCandidate g)
  (globalControlL2 g)
  (globalControlF4 g)

GRUEquivalent : GRUState → GRUState → Set
GRUEquivalent s t = persistentGRU s ≡ persistentGRU t

gruStep-respects-equivalence : ∀ K a s t → GRUEquivalent s t →
  GRUEquivalent (gruStep K s a) (gruStep K t a)
gruStep-respects-equivalence K a s t eq =
  cong (λ h →
    h , int8Add (gruInputMatrix s) (rightKey a) , int8Add (gruRecurrentMatrix s) (rightKey a) ,
    int8Add (gruBias s) (leftKey a) , noiseUpdate s , noiseReset s , noiseCandidate s ,
    globalControlL2 s)
    eq

record F4IntUState : Set where
  constructor f4IntUState
  field theta0 theta1 theta2 theta3 : Int8
        stepCount : Nat
open F4IntUState public

f4ThetaStep : F4IntUState → Int8 → F4IntUState
f4ThetaStep θ g = f4IntUState
  (int8Add (theta0 θ) g)
  (int8Add (theta1 θ) g)
  (int8Add (theta2 θ) g)
  (int8Add (theta3 θ) g)
  (suc (stepCount θ))

record NormPair : Set where
  constructor normPair
  field l1Weight pathNorm : Nat
open NormPair public

record FullLearnerState : Set₁ where
  constructor fullLearnerState
  field
    clock : Nat
    watkins : WatkinsState
    attention : LearnedSparsemaxAttention
    gru : GRUState
    optimizer : F4IntUState
    norm : NormPair
    lcbCounts : LCBCountState
    qLogControl : Int8 × Int8
    qLogValue : FiniteRational
open FullLearnerState public

record FullLearnerKernel : Set₁ where
  constructor fullLearnerKernel
  field
    watkinsKernel : WatkinsKernel
    attentionKernel : LearnedSparsemaxAttention → LearnedSparsemaxAttention
    gruKernel : FullLearnerKernel → GRUState → LearnedSparsemaxAttention → GRUState
    optimizerKernel : Int8 → F4IntUState → F4IntUState
    lcbKernel : LCBCountState → LCBCountState
    qLogKernel : Int8 → FiniteRational
open FullLearnerKernel public

canonicalQScores : FullLearnerKernel → FullLearnerState → ActionScore
canonicalQScores K s = lcbScore (record { bonus = finiteLCBBonus8 }) (lcbCounts s) (critic (watkins s))

canonicalWatkinsStep : FullLearnerKernel → FullLearnerState → WatkinsState
canonicalWatkinsStep K s = watkinsStep (watkinsKernel K) (watkins s)

canonicalAttentionInput : FullLearnerKernel → FullLearnerState → LearnedSparsemaxAttention
canonicalAttentionInput K s = attentionKernel K (attention s)

canonicalAttentionStep : FullLearnerKernel → FullLearnerState → LearnedSparsemaxAttention
canonicalAttentionStep K s = learnedSparsemaxAttention (fixedTemperatureSparsemax (canonicalQScores K s))

canonicalGRUStep : FullLearnerKernel → FullLearnerState → GRUState
canonicalGRUStep K s = gruKernel K (gru s) (canonicalAttentionStep K s)

canonicalSignal : FullLearnerKernel → FullLearnerState → Int8
canonicalSignal K s = signal (canonicalWatkinsStep K s)

canonicalOptimizerStep : FullLearnerKernel → FullLearnerState → F4IntUState
canonicalOptimizerStep K s = optimizerKernel K (canonicalSignal K s) (optimizer s)

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

canonicalStep-not-fixed : ∀ K s → canonicalFullStep K s ≢ s
canonicalStep-not-fixed K s eq =
  plus-suc-not-self (clock s) zero
    (trans (plus-suc (clock s) zero)
      (trans (cong suc (plus-zero (clock s)))
        (trans (sym (canonicalFullStep-clock K s)) (cong clock eq))))

iterateCanonical : FullLearnerKernel → Nat → FullLearnerState → FullLearnerState
iterateCanonical K zero s = s
iterateCanonical K (suc n) s = canonicalFullStep K (iterateCanonical K n s)

clockAfter : ∀ K n s → clock (iterateCanonical K n s) ≡ clock s + n
clockAfter K zero s = refl
clockAfter K (suc n) s = trans (cong suc (clockAfter K n s)) (sym (plus-suc (clock s) n))

canonicalAperiodic : ∀ K s n → iterateCanonical K (suc n) s ≢ s
canonicalAperiodic K s n cyc = plus-suc-not-self (clock s) n
  (trans (sym (clockAfter K (suc n) s)) (cong clock cyc))
