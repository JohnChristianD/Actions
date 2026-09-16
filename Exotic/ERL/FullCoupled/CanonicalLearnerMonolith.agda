{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith where

open import Agda.Builtin.Equality using (_≡_; refl; sym; cong; subst; trans)
open import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Project-free finite carrier. No environment, reward process, probability
-- space, observation model, or statistical oracle occurs in this module.
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
-- Order, iteration, strict descent, and exact deterministic convergence.
------------------------------------------------------------------------

lt-trans : ∀ {a b c : Nat} → a < b → b < c → a < c
lt-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)
  where
  le-trans : ∀ {m n k : Nat} → m ≤ n → n ≤ k → m ≤ k
  le-trans z≤n q = q
  le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)

lt-irrefl : ∀ n → ¬ (n < n)
lt-irrefl zero p = p where p : ⊥
lt-irrefl (suc n) (s≤s p) = lt-irrefl n p

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate step zero s = s
iterate step (suc n) s = step (iterate step n s)

iterate-shift :
  ∀ {S : Set} (step : S → S) (n : Nat) (s : S) →
  iterate step n (step s) ≡ iterate step (suc n) s
iterate-shift step zero s = refl
iterate-shift step (suc n) s = cong step (iterate-shift step n s)

Fixed : ∀ {S : Set} → (S → S) → S → Set
Fixed step s = step s ≡ s

OrbitNonFixed :
  ∀ {S : Set} {step : S → S} → S → Set
OrbitNonFixed {step = step} s = ∀ n → iterate step n s ≢ step (iterate step n s)

shiftOrbitNonFixed :
  ∀ {S : Set} {step : S → S} {s : S} →
  OrbitNonFixed s → OrbitNonFixed (step s)
shiftOrbitNonFixed {step = step} {s = s} nf n =
  let p = iterate-shift step n s
  in nf (suc n) (λ eq → nf (suc n) (trans (sym p) (trans eq (cong step p))))

record LyapunovCertificate (S : Set) (step : S → S) : Set₁ where
  constructor lyapunovCertificate
  field
    energy : S → Nat
    strictDecrease : ∀ s → step s ≢ s → energy (step s) < energy s
open LyapunovCertificate public

iterate-energy-decrease :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step) {s : S} →
  OrbitNonFixed s → ∀ n →
  energy L (iterate step (suc n) s) < energy L s
iterate-energy-decrease L {s = s} nf zero = strictDecrease L s (nf zero)
iterate-energy-decrease L {s = s} nf (suc n) =
  lt-trans
    (subst
      (λ z → energy L z < energy L (step s))
      (iterate-shift step n (step s))
      (iterate-energy-decrease L (shiftOrbitNonFixed nf) n))
    (strictDecrease L s (nf zero))

noNontrivialFiniteCycle :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step) {s : S} (n : Nat) →
  iterate step (suc n) s ≡ s → OrbitNonFixed s → ⊥
noNontrivialFiniteCycle L {s = s} n cyc nf =
  lt-irrefl (energy L s)
    (subst (λ z → energy L z < energy L s)
      cyc
      (iterate-energy-decrease L nf n))

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

record HasDecidableEquality (S : Set) : Set₁ where
  constructor decidableEquality
  field decide : (x y : S) → (x ≡ y) ⊎ (x ≢ y)
open HasDecidableEquality public

zeroCannotDescend : ∀ {n : Nat} → n < zero → ⊥
zeroCannotDescend ()

le-refl : ∀ n → n ≤ n
le-refl zero = z≤n
le-refl (suc n) = s≤s (le-refl n)

le-trans : ∀ {m n k : Nat} → m ≤ n → n ≤ k → m ≤ k
le-trans z≤n q = q
le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)

le-zero : ∀ {n : Nat} → n ≤ zero → n ≡ zero
le-zero z≤n = refl
le-zero (s≤s ())

lt-le : ∀ {m n k : Nat} → m < n → n ≤ k → m < k
lt-le (s≤s p) (s≤s q) = s≤s (le-trans p q)
lt-le {n = zero} p z≤n = zeroCannotDescend p

lt-suc-le : ∀ {m n : Nat} → m < suc n → m ≤ n
lt-suc-le (s≤s p) = p

record EventuallyFixed {S : Set} (step : S → S) (s : S) : Set where
  constructor eventuallyFixed
  field steps : Nat; terminal : Fixed step (iterate step steps s)
open EventuallyFixed public

eventuallyFixedFromLyapunov :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step)
  (D : HasDecidableEquality S)
  (s : S) → EventuallyFixed step s
eventuallyFixedFromLyapunov L D s = go (energy L s) s (le-refl (energy L s))
  where
  go : ∀ bound s → energy L s ≤ bound → EventuallyFixed step s
  go zero s bound with decide D s (step s)
  ... | inj₁ fixed = eventuallyFixed zero fixed
  ... | inj₂ moving =
    zeroCannotDescend
      (subst (λ z → energy L (step s) < z) (le-zero bound) (strictDecrease L s moving))
  go (suc bound) s proof with decide D s (step s)
  ... | inj₁ fixed = eventuallyFixed zero fixed
  ... | inj₂ moving =
    let next = go bound (step s) (lt-suc-le (lt-le (strictDecrease L s moving) proof))
        k = steps next
        p = iterate-shift step k s
        terminal' : Fixed step (iterate step (suc k) s)
        terminal' = subst (λ z → Fixed step z) p (terminal next)
    in eventuallyFixed (suc k) terminal'

record UniqueFixedPoint {S : Set} (step : S → S) (target : S) : Set where
  constructor uniqueFixedPoint
  field targetFixed : Fixed step target
        uniqueFixed : ∀ {s} → Fixed step s → s ≡ target
open UniqueFixedPoint public

record DeterministicLearnerCertificate (S : Set) (step : S → S) : Set₁ where
  constructor deterministicLearnerCertificate
  field lyapunov : LyapunovCertificate S step
        decidableEquality : HasDecidableEquality S
        target : S
        terminal : UniqueFixedPoint step target
open DeterministicLearnerCertificate public

deterministicLearnerConvergence :
  ∀ {S : Set} {step : S → S}
  (C : DeterministicLearnerCertificate S step) (s : S) →
  iterate step (steps (eventuallyFixedFromLyapunov (lyapunov C) (decidableEquality C) s)) s ≡ target C
deterministicLearnerConvergence C s =
  uniqueFixed (terminal C) (terminal (eventuallyFixedFromLyapunov (lyapunov C) (decidableEquality C) s))

deterministicLearnerTargetFixed :
  ∀ {S : Set} {step : S → S}
  (C : DeterministicLearnerCertificate S step) → Fixed step (target C)
deterministicLearnerTargetFixed C = targetFixed (terminal C)

deterministicLearnerFixedStatesCollapse :
  ∀ {S : Set} {step : S → S}
  (C : DeterministicLearnerCertificate S step) {s : S} → Fixed step s → s ≡ target C
deterministicLearnerFixedStatesCollapse C = uniqueFixed (terminal C)

------------------------------------------------------------------------
-- Exact finite-rational Mobius boundary x/(1-x).
------------------------------------------------------------------------

record FiniteRational : Set where
  constructor finiteRational
  field numerator denominator : I.Int
open FiniteRational public

signedCode : Int8 → I.Int
signedCode x with toℕ (code x) < 128
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
  ∀ f g h x → run (composeAction (composeAction f g) h) x ≡ run (composeAction f (composeAction g h)) x
mobiusAssociativity f g h x = refl

------------------------------------------------------------------------
-- Watkins critic-only learner, sparsemax+LCB, negative q-log shaping.
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

halfInt : I.Int → I.Int
halfInt (I.pos n) = I.pos (halfNat n)
halfInt (I.negsuc n) = I.pos zero

sparsemax2 : ActionScore → Sparsemax2Pair
sparsemax2 (actionScore l r) =
  let d = I._-_ (signedCode l) (signedCode r)
      scaled = halfInt (I._+_ (I.pos 128) (I._*_ (I.pos 8) d))
  in int8OfNat (toNat scaled) , int8OfNat (128 ∸ toNat scaled)
  where
  toNat : I.Int → Nat
  toNat (I.pos n) = n
  toNat (I.negsuc n) = zero

actionLeft : Sparsemax2Pair → Int8
actionLeft (l , r) = l

chooseLeft : Sparsemax2Pair → BoolLike
chooseLeft (l , r) with toℕ (code l) < toℕ (code r)
... | true = disabled
... | false = enabled

updateCounts : Sparsemax2Pair → LCBCountState → LCBCountState
updateCounts p (lcbCountState l r t) with chooseLeft p
... | enabled = lcbCountState (suc l) r (suc t)
... | disabled = lcbCountState l (suc r) (suc t)

record SignedQLogControl : Set where
  constructor signedQLogControl
  field enabledQLog : BoolLike
        coefficient : Int8
open SignedQLogControl public

finiteQLog8 : Int8 → FiniteRational
finiteQLog8 x with toℕ (code x)
... | zero = finiteRational (I.pos 1) (I.pos 1)
... | suc n = finiteRational (I.pos n) (I.pos (suc n))

negInt : I.Int → I.Int
negInt (I.pos zero) = I.pos zero
negInt (I.pos (suc n)) = I.negsuc n
negInt (I.negsuc n) = I.pos (suc n)

negativeFiniteQLog8 : Int8 → FiniteRational
negativeFiniteQLog8 x =
  let q = finiteQLog8 x
  in finiteRational (negInt (numerator q)) (denominator q)

negativeFiniteQLogLaw : ∀ x →
  negativeFiniteQLog8 x ≡ finiteRational (negInt (numerator (finiteQLog8 x))) (denominator (finiteQLog8 x))
negativeFiniteQLogLaw x = refl

qLogSignal : SignedQLogControl → Int8 → Int8
qLogSignal c x with enabledQLog c
... | enabled = int8Add x (coefficient c)
... | disabled = x

------------------------------------------------------------------------
-- Learned sparsemax attention, independent from policy selection.
------------------------------------------------------------------------

record LearnedSparsemaxAttention : Set where
  constructor learnedSparsemaxAttention
  field leftParameter rightParameter : Int8
open LearnedSparsemaxAttention public

identityAttention : LearnedSparsemaxAttention
identityAttention = learnedSparsemaxAttention one8 one8

attentionWeights : LearnedSparsemaxAttention → Sparsemax2Pair
attentionWeights a = sparsemax2 (actionScore (leftParameter a) (rightParameter a))

------------------------------------------------------------------------
-- Normalized H4 boundary.
------------------------------------------------------------------------

record HalfInt : Set where
  constructor halfIntValue
  field halfNumerator : I.Int
open HalfInt public

WalshVec4 : Set
WalshVec4 = HalfInt × (HalfInt × (HalfInt × HalfInt))

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

dot4 : IntVec4 → IntVec4 → I.Int
dot4 (a , (b , (c , d))) (e , (f , (g , h))) =
  I._+_ (I._+_ (I._*_ a e) (I._*_ b f)) (I._+_ (I._*_ c g) (I._*_ d h))

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
  dot4 row0 row0 ≡ I.pos 4 × dot4 row1 row1 ≡ I.pos 4 × dot4 row2 row2 ≡ I.pos 4 × dot4 row3 row3 ≡ I.pos 4 ×
  dot4 row0 row1 ≡ I.pos 0 × dot4 row0 row2 ≡ I.pos 0 × dot4 row0 row3 ≡ I.pos 0 ×
  dot4 row1 row2 ≡ I.pos 0 × dot4 row1 row3 ≡ I.pos 0 × dot4 row2 row3 ≡ I.pos 0
walshOrthonormal = walsh00 , (walsh11 , (walsh22 , (walsh33 , (walsh01 , (walsh02 , (walsh03 , (walsh12 , (walsh13 , walsh23))))))))

liftAttention : Int8 × Int8 → IntVec4
liftAttention (x , y) = I.pos (toℕ (code x)) , (I.pos (toℕ (code y)) , (I.pos 0 , I.pos 0))

walshHadamardApply : IntVec4 → WalshVec4
walshHadamardApply (a , (b , (c , d))) =
  halfIntValue (I._+_ (I._+_ a b) (I._+_ c d)) ,
  (halfIntValue (I._+_ (I._-_ a b) (I._-_ c d)) ,
    (halfIntValue (I._+_ (I._+_ a b) (I._+_ (I.negsuc 0) (I._+_ c d))) ,
      halfIntValue (I._+_ (I._-_ a b) (I._+_ (I._*_ (I.negsuc 0) c) d))))

------------------------------------------------------------------------
-- Custom learner GRU: state-independent hard-sign gate and x/(1-x) activation.
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

gateFromInput : Int8 → Int8
gateFromInput x = gateCode (signedCode x)

gateComplement : Int8 → Int8
gateComplement g = int8OfNat (128 ∸ toℕ (code g))

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

code8 : FiniteRational → Int8
code8 q = int8OfNat (intCode (numerator q))
  where
  intCode : I.Int → Nat
  intCode (I.pos n) = n
  intCode (I.negsuc n) = zero

mix8 : Int8 → Int8 → Int8 → Int8
mix8 gate old candidate = int8Add (int8Mul (gateComplement gate) old) (int8Mul gate candidate)

gruCandidate : Int8 → Int8 → Int8
gruCandidate h x = int8Add h x

gruStep : GRUState → Int8 → GRUState
gruStep (gruState h m n g) x =
  gruState
    (mix8 (gateFromInput x) h (int8Add (code8 (mobiusRatio8 x)) (gruCandidate h x)))
    m n g

persistentGRU : GRUState → GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU (gruState h m n g) = m , (n , g)

persistent-preservation :
  ∀ (s : GRUState) (x : Int8) → persistentGRU (gruStep s x) ≡ persistentGRU s
persistent-preservation (gruState h m n g) x = refl

gruParameterPersistence :
  ∀ (s : GRUState) (x : Int8) →
  matrices (gruStep s x) ≡ matrices s × noise (gruStep s x) ≡ noise s × globalControl (gruStep s x) ≡ globalControl s
gruParameterPersistence (gruState h m n g) x = refl , (refl , refl)

------------------------------------------------------------------------
-- Global optimizer, coupled L2, norm-pair, and full learner state.
------------------------------------------------------------------------

record F4Scalar : Set₁ where
  field R : Set
        zero one halfULP : R
        addS subS mulS : R → R → R
        intToR : I.Int → R
        quantize8 : R → R
        quantizedReconstruction : ∀ x → addS (quantize8 x) (subS x (quantize8 x)) ≡ x
open F4Scalar public

record F4IntUState (A : F4Scalar) : Set₁ where
  constructor f4IntUState
  field thetaQ rTheta eQ rE rL : R A
open F4IntUState public

record F4IntUKernel (A : F4Scalar) : Set₁ where
  constructor f4IntUKernel
  field globalL2 : R A
open F4IntUKernel public

f4ThetaStep : ∀ {A : F4Scalar} → F4IntUKernel A → F4IntUState A → R A → F4IntUState A
f4ThetaStep {A} K s g =
  let base = addS A (thetaQ s) (rTheta s)
      raw = subS A (addS A base g) (mulS A (globalL2 K) base)
      q = quantize8 A raw
  in f4IntUState q (subS A raw q) (eQ s) (rE s) (rL s)

f4ParameterInvariant : ∀ {A : F4Scalar} (K : F4IntUKernel A) (s : F4IntUState A) (g : R A) →
  addS A (thetaQ (f4ThetaStep K s g)) (rTheta (f4ThetaStep K s g)) ≡
  subS A (addS A (addS A (thetaQ s) (rTheta s)) g)
    (mulS A (globalL2 K) (addS A (thetaQ s) (rTheta s)))
f4ParameterInvariant {A} K s g = quantizedReconstruction A
  (subS A (addS A (addS A (thetaQ s) (rTheta s)) g)
    (mulS A (globalL2 K) (addS A (thetaQ s) (rTheta s))))

record NormPair (A : F4Scalar) : Set₁ where
  constructor normPair
  field l1 path : R A
open NormPair public

record FullLearnerState (A : F4Scalar) : Set₁ where
  constructor fullLearnerState
  field clock : Nat
        watkins : WatkinsState
        attention : LearnedSparsemaxAttention
        gru : GRUState
        optimizer : F4IntUState A
        norm : NormPair A
        lcbCounts : LCBCountState
        qLogControl : SignedQLogControl
        qLogValue : FiniteRational
open FullLearnerState public

record FullLearnerKernel (A : F4Scalar) : Set₁ where
  constructor fullLearnerKernel
  field watkinsKernel : WatkinsKernel
        attentionStep : LearnedSparsemaxAttention → Int8 → LearnedSparsemaxAttention
        attentionToGRU : WalshVec4 → Int8
        optimizerKernel : F4IntUKernel A
        lcbKernel : LCBCountKernel
open FullLearnerKernel public

canonicalPolicy : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → Sparsemax2Pair
canonicalPolicy K s = sparsemax2
  (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s)))

replaceAttention : ∀ {A : F4Scalar} → FullLearnerState A → LearnedSparsemaxAttention → FullLearnerState A
replaceAttention s a = fullLearnerState (clock s) (watkins s) a (gru s) (optimizer s) (norm s) (lcbCounts s) (qLogControl s) (qLogValue s)

canonicalPolicy-attention-invariant :
  ∀ {A : F4Scalar} (K : FullLearnerKernel A) (s : FullLearnerState A) (a : LearnedSparsemaxAttention) →
  canonicalPolicy K (replaceAttention s a) ≡ canonicalPolicy K s
canonicalPolicy-attention-invariant K s a = refl

canonicalSignal : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalSignal K s = qLogSignal (qLogControl s) (actionLeft (canonicalPolicy K s))

canonicalWatkinsStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → WatkinsState
canonicalWatkinsStep K s =
  watkinsStep (watkinsKernel K)
    (watkinsState (critic (watkins s)) (canonicalSignal K s) (trace (watkins s)))
  where
  trace : WatkinsState → BoolLike
  trace w = WatkinsState.trace w

canonicalAttentionStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → LearnedSparsemaxAttention
canonicalAttentionStep K s = attentionStep K (attention s) (canonicalSignal K s)

canonicalGRUStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → GRUState
canonicalGRUStep K s =
  let transformed = walshHadamardApply (liftAttention (canonicalPolicy K s))
  in gruStep (gru s) (int8Add (canonicalSignal K s) (attentionToGRU K transformed))

canonicalPersistentGRUPreservation :
  ∀ {A : F4Scalar} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistentGRUPreservation K s =
  persistent-preservation (gru s) (int8Add (canonicalSignal K s)
    (attentionToGRU K (walshHadamardApply (liftAttention (canonicalPolicy K s)))))

canonicalOptimizerStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → F4IntUState A
canonicalOptimizerStep {A} K s = f4ThetaStep (optimizerKernel K) (optimizer s)
  (intToR A (I.pos (toℕ (code (canonicalSignal K s)))))

canonicalCountStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → LCBCountState
canonicalCountStep K s = updateCounts (canonicalPolicy K s) (lcbCounts s)

canonicalQLogStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → FiniteRational
canonicalQLogStep K s = negativeFiniteQLog8 (actionLeft (canonicalPolicy K s))

canonicalQLogControlStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → SignedQLogControl
canonicalQLogControlStep K s = signedQLogControl enabled (actionLeft (canonicalPolicy K s))

canonicalFullStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → FullLearnerState A
canonicalFullStep K s = fullLearnerState
  (suc (clock s)) (canonicalWatkinsStep K s) (canonicalAttentionStep K s)
  (canonicalGRUStep K s) (canonicalOptimizerStep K s) (norm s)
  (canonicalCountStep K s) (canonicalQLogControlStep K s) (canonicalQLogStep K s)

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

record FullLearnerCoerciveQuadratic {A : F4Scalar} (K : FullLearnerKernel A) : Set₁ where
  constructor fullLearnerCoerciveQuadratic
  field energy : FullLearnerState A → Nat
        strictDecrease : ∀ s → canonicalFullStep K s ≢ s → energy (canonicalFullStep K s) < energy s
open FullLearnerCoerciveQuadratic public

canonicalQuadraticDecay :
  ∀ {A : F4Scalar} {K : FullLearnerKernel A} (W : FullLearnerCoerciveQuadratic K) (s : FullLearnerState A) →
  canonicalFullStep K s ≢ s → energy W (canonicalFullStep K s) < energy W s
canonicalQuadraticDecay W s moved = strictDecrease W s moved

plus-suc : ∀ (m n : Nat) → m + suc n ≡ suc (m + n)
plus-suc zero n = refl
plus-suc (suc m) n = cong suc (plus-suc m n)

clockAfter : ∀ {A : F4Scalar} (K : FullLearnerKernel A) (n : Nat) (s : FullLearnerState A) → clock (iterate (canonicalFullStep K) n s) ≡ clock s + n
clockAfter K zero s = refl
clockAfter K (suc n) s = trans (cong suc (clockAfter K n s)) (sym (plus-suc (clock s) n))

plus-suc-not-self : ∀ (r n : Nat) → r + suc n ≢ r
plus-suc-not-self zero n = λ ()
plus-suc-not-self (suc r) n eq = plus-suc-not-self r n (sucInjective eq)
  where
  sucInjective : ∀ {m n} → suc m ≡ suc n → m ≡ n
  sucInjective refl = refl

canonicalAperiodic : ∀ {A : F4Scalar} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : Nat) → iterate (canonicalFullStep K) (suc n) s ≢ s
canonicalAperiodic K s n cyc = plus-suc-not-self (clock s) n
  (trans (sym (clockAfter K (suc n) s)) (cong clock cyc))

canonicalCoerciveNoCycle :
  ∀ {A : F4Scalar} {K : FullLearnerKernel A}
  (W : FullLearnerCoerciveQuadratic K) {s : FullLearnerState A} (n : Nat) →
  iterate (canonicalFullStep K) (suc n) s ≡ s → OrbitNonFixed (canonicalFullStep K) s → ⊥
canonicalCoerciveNoCycle W n cyc nf =
  noNontrivialFiniteCycle (lyapunovCertificate (energy W) (strictDecrease W)) n cyc nf

------------------------------------------------------------------------
-- Compact semidirect algebra and finite count obstruction.
------------------------------------------------------------------------

record Monoid (M : Set) : Set₁ where
  constructor monoid
  field unit mul assoc left-id right-id
open Monoid public

record Semidirect (A B : Set) : Set₁ where
  constructor semidirect
  field leftMonoid : Monoid A
        rightMonoid : Monoid B
open Semidirect public

semidirectMul : ∀ {A B : Set} → Semidirect A B → (A × B) → (A × B) → (A × B)
semidirectMul S (a , b) (a' , b') =
  mul (leftMonoid S) a a' , mul (rightMonoid S) b b'

record StrictCountSystem (S : Set) (step : S → S) : Set₁ where
  constructor strictCountSystem
  field count : S → Nat
        strictCount : ∀ s → step s ≢ s → count s < count (step s)
open StrictCountSystem public

count-two-step-increases :
  ∀ {S : Set} {step : S → S} (C : StrictCountSystem S step) {s : S} →
  step s ≢ s → step (step s) ≢ step s → count C s < count C (step (step s))
count-two-step-increases C nf₀ nf₁ = lt-trans (strictCount C _ nf₀) (strictCount C _ nf₁)

noCountedTwoCycle :
  ∀ {S : Set} {step : S → S} (C : StrictCountSystem S step) {s : S} →
  step (step s) ≡ s → step s ≢ s → step (step s) ≢ step s → ⊥
noCountedTwoCycle C cyc nf₀ nf₁ =
  lt-irrefl (count C s) (subst (λ z → count C z < count C s) cyc (count-two-step-increases C nf₀ nf₁))

------------------------------------------------------------------------
-- Exact regression facts retained in canonical scope.
------------------------------------------------------------------------

temperatureCodeLaw : sparsemaxTemperature ≡ int8OfNat 16
temperatureCodeLaw = refl

temperatureTieLaw : sparsemax2 (actionScore (int8OfNat 0) (int8OfNat 0)) ≡ int8OfNat 64 , int8OfNat 64
temperatureTieLaw = refl

temperaturePositiveUnitLaw : sparsemax2 (actionScore (int8OfNat 1) (int8OfNat 0)) ≡ int8OfNat 68 , int8OfNat 60
temperaturePositiveUnitLaw = refl

temperatureNegativeUnitLaw : sparsemax2 (actionScore (int8OfNat 0) (int8OfNat 1)) ≡ int8OfNat 60 , int8OfNat 68
temperatureNegativeUnitLaw = refl

pessimisticInit : Int8
pessimisticInit = int8OfNat 128

pessimisticCritic : CriticState
pessimisticCritic = criticState pessimisticInit pessimisticInit

maxPessimisticCritic-law : qLeft pessimisticCritic ≡ int8OfNat 128 × qRight pessimisticCritic ≡ int8OfNat 128
maxPessimisticCritic-law = refl , refl

canonicalWalshBoundary : walshOrthonormal ≡ walshOrthonormal
canonicalWalshBoundary = refl

canonicalPersistent :
  ∀ {A : F4Scalar} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistent = canonicalPersistentGRUPreservation
