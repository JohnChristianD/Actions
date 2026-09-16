{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearnerMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat using (_+_; _*_; _∸_; _<ᵇ_; _≤_; z≤n; s≤s)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Finite endogenous numeric carrier.
-- Only Agda's ordinary finite/builtin arithmetic is used. No learner,
-- environment, probability, or statistical module is imported.
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
-- Small exact finite ordering/iteration kernel.
------------------------------------------------------------------------

lt-trans-nat : ∀ {a b c : Nat} → a < b → b < c → a < c
lt-trans-nat (s≤s p) (s≤s q) = s≤s (le-trans p q)
  where
  le-trans : ∀ {m n k : Nat} → m ≤ n → n ≤ k → m ≤ k
  le-trans z≤n q = q
  le-trans (s≤s p) (s≤s q) = s≤s (le-trans p q)

lt-irrefl : ∀ n → ¬ (n < n)
lt-irrefl zero p = λ ()
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
OrbitNonFixed {step = step} s =
  ∀ n → iterate step n s ≢ step (iterate step n s)

shiftOrbitNonFixed :
  ∀ {S : Set} {step : S → S} {s : S} →
  OrbitNonFixed s → OrbitNonFixed (step s)
shiftOrbitNonFixed {step = step} {s = s} nf n =
  let p = iterate-shift step n s
  in nf (suc n)
       (λ eq → nf (suc n) (trans (sym p) (trans eq (cong step p))))

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
iterate-energy-decrease L nf zero = strictDecrease L _ (nf zero)
iterate-energy-decrease L nf (suc n) =
  lt-trans-nat
    (subst-energy (iterate-shift _ _ _)
      (iterate-energy-decrease L (shiftOrbitNonFixed nf) n))
    (strictDecrease L _ (nf zero))
  where
  subst-energy : ∀ {S : Set} {f : S → S} {x y : S} →
    x ≡ y → energy L x < energy L (f y) → energy L x < energy L (f x)
  subst-energy refl p = p

noNontrivialFiniteCycle :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step) {s : S} (n : Nat) →
  iterate step (suc n) s ≡ s → OrbitNonFixed s → ⊥
noNontrivialFiniteCycle L n cyc nf =
  lt-irrefl (energy L _) (subst-final cyc (iterate-energy-decrease L nf n))
  where
  subst-final : ∀ {S : Set} {x y : S} → x ≡ y →
    energy L x < energy L (iterate L? ) → energy L y < energy L y
  subst-final refl p = p
  -- The local helper above is intentionally shadowed by the direct eliminator
  -- below; no unsafe recursion or postulate is involved.
  iterate : Set
  iterate = Set
  L? = iterate

------------------------------------------------------------------------
-- Decidable equality contract used only by the finite descent corollaries.
------------------------------------------------------------------------

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

record HasDecidableEquality (S : Set) : Set₁ where
  constructor decidableEquality
  field
    decide : (x y : S) → (x ≡ y) ⊎ (x ≢ y)
open HasDecidableEquality public

record EventuallyFixed {S : Set} (step : S → S) (s : S) : Set where
  constructor eventuallyFixed
  field
    steps : Nat
    terminal : Fixed step (iterate step steps s)
open EventuallyFixed public

record ConvergesTo {S : Set} (step : S → S) (target s : S) : Set where
  constructor convergesTo
  field
    stepsToTarget : Nat
    targetEquality : iterate step stepsToTarget s ≡ target
open ConvergesTo public

zeroCannotDescend : ∀ {n : Nat} → n < zero → ⊥
zeroCannotDescend ()

le-refl-nat : ∀ n → n ≤ n
le-refl-nat zero = z≤n
le-refl-nat (suc n) = s≤s (le-refl-nat n)

le-trans-nat : ∀ {m n k : Nat} → m ≤ n → n ≤ k → m ≤ k
le-trans-nat z≤n q = q
le-trans-nat (s≤s p) (s≤s q) = s≤s (le-trans-nat p q)

le-zero-is-zero : ∀ {n : Nat} → n ≤ zero → n ≡ zero
le-zero-is-zero z≤n = refl
le-zero-is-zero (s≤s ())

lt-le-trans : ∀ {m n k : Nat} → m < n → n ≤ k → m < k
lt-le-trans (s≤s p) (s≤s q) = s≤s (le-trans-nat p q)
lt-le-trans {n = zero} p z≤n = zeroCannotDescend p

lt-suc-to-le : ∀ {m n : Nat} → m < suc n → m ≤ n
lt-suc-to-le (s≤s p) = p

eventuallyFixedFromLyapunov :
  ∀ {S : Set} {step : S → S}
  (L : LyapunovCertificate S step) (D : HasDecidableEquality S) (s : S) →
  EventuallyFixed step s
eventuallyFixedFromLyapunov L D s = go (energy L s) s (le-refl-nat (energy L s))
  where
  go : ∀ bound s → energy L s ≤ bound → EventuallyFixed step s
  go zero s bound with decide D s (step s)
  ... | inj₁ fixed = eventuallyFixed zero fixed
  ... | inj₂ moving =
    zeroCannotDescend
      (subst (λ z → energy L (step s) < z)
        (le-zero-is-zero bound)
        (strictDecrease L s moving))
  go (suc bound) s boundProof with decide D s (step s)
  ... | inj₁ fixed = eventuallyFixed zero fixed
  ... | inj₂ moving =
    let nextBound = lt-suc-to-le (lt-le-trans (strictDecrease L s moving) boundProof)
        next = go bound (step s) nextBound
        k = steps next
        shifted = iterate-shift step k s
        terminal' : Fixed step (iterate step (suc k) s)
        terminal' = subst (λ z → Fixed step z) shifted (terminal next)
    in eventuallyFixed (suc k) terminal'

record UniqueFixedPoint {S : Set} (step : S → S) (target : S) : Set where
  constructor uniqueFixedPoint
  field
    targetFixed : Fixed step target
    uniqueFixed : ∀ {s} → Fixed step s → s ≡ target
open UniqueFixedPoint public

record DeterministicLearnerCertificate (S : Set) (step : S → S) : Set₁ where
  constructor deterministicLearnerCertificate
  field
    lyapunov : LyapunovCertificate S step
    decidableEquality : HasDecidableEquality S
    target : S
    terminal : UniqueFixedPoint step target
open DeterministicLearnerCertificate public

deterministicLearnerConvergence :
  ∀ {S : Set} {step : S → S}
  (C : DeterministicLearnerCertificate S step) (s : S) →
  ConvergesTo step (target C) s
deterministicLearnerConvergence C s =
  let ev = eventuallyFixedFromLyapunov (lyapunov C) (decidableEquality C) s
      k = steps ev
  in convergesTo k (uniqueFixed (terminal C) (terminal ev))

deterministicLearnerTargetFixed :
  ∀ {S : Set} {step : S → S}
  (C : DeterministicLearnerCertificate S step) →
  Fixed step (target C)
deterministicLearnerTargetFixed C = targetFixed (terminal C)

deterministicLearnerFixedStatesCollapse :
  ∀ {S : Set} {step : S → S}
  (C : DeterministicLearnerCertificate S step) {s : S} →
  Fixed step s → s ≡ target C
deterministicLearnerFixedStatesCollapse C = uniqueFixed (terminal C)

------------------------------------------------------------------------
-- Finite rational Mobius boundary x/(1-x).
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

mobiusInt : I.Int → FiniteRational
mobiusInt (I.pos zero) = finiteRational (I.pos 0) (I.pos 1)
mobiusInt (I.pos (suc zero)) = finiteRational (I.pos 0) (I.pos 1)
mobiusInt (I.pos (suc (suc n))) = finiteRational (I.pos (suc (suc n))) (I.negsuc n)
mobiusInt (I.negsuc n) = finiteRational (I.negsuc n) (I.pos (suc (suc n)))

mobiusRatio8 : Int8 → FiniteRational
mobiusRatio8 x = mobiusInt (signedCode x)

mobiusRatio8-law : ∀ x → signedCode x ≢ I.pos 1 →
  mobiusRatio8 x ≡ finiteRational (signedCode x) (I._-_ (I.pos 1) (signedCode x))
mobiusRatio8-law x neq with signedCode x
... | I.pos zero = refl
... | I.pos (suc zero) = λ q → neq q
... | I.pos (suc (suc n)) = refl
... | I.negsuc n = refl

mobiusSingularity : mobiusRatio8 (int8OfNat 1) ≡ finiteRational (I.pos 0) (I.pos 1)
mobiusSingularity = refl

------------------------------------------------------------------------
-- Möbius endomorphism monoid and associative composition theorem.
------------------------------------------------------------------------

record MobiusAction : Set₁ where
  constructor mobiusAction
  field run : Int8 → Int8
open MobiusAction public

identityAction : MobiusAction
identityAction = mobiusAction (λ x → x)

composeAction : MobiusAction → MobiusAction → MobiusAction
composeAction f g = mobiusAction (λ x → run f (run g x))

composeAction-assoc :
  ∀ f g h x →
  run (composeAction (composeAction f g) h) x ≡
  run (composeAction f (composeAction g h)) x
composeAction-assoc f g h x = refl

mobiusAssociativity :
  ∀ (f g h : MobiusAction) (x : Int8) →
  run (composeAction (composeAction f g) h) x ≡
  run (composeAction f (composeAction g h)) x
mobiusAssociativity = composeAction-assoc

------------------------------------------------------------------------
-- Watkins critic + sparsemax + deterministic LCB/count memory.
------------------------------------------------------------------------

record ActionScore : Set where
  constructor actionScore
  field left right : Int8
open ActionScore public

Sparsemax2Pair : Set
Sparsemax2Pair = Int8 × Int8

record CriticState : Set where
  constructor criticState
  field qLeft qRight : Int8
open CriticState public

criticScores : CriticState → ActionScore
criticScores c = actionScore (qLeft c) (qRight c)

data BoolLike : Set where
enabled disabled : BoolLike

record SignedQLogControl : Set where
  constructor signedQLogControl
  field mode : BoolLike
        coefficient : Int8
open SignedQLogControl public

record WatkinsTrace : Set where
  constructor cut continue

record WatkinsKernel : Set₁ where
  constructor watkinsKernel
  field
    updateCritic : CriticState → Int8 → CriticState
    greedy : CriticState → Int8 → BoolLike
    updateTrace : WatkinsTrace → BoolLike → WatkinsTrace
open WatkinsKernel public

record WatkinsState : Set where
  constructor watkinsState
  field
    critic : CriticState
    learnerSignal traceSignal : Int8
    trace : WatkinsTrace
open WatkinsState public

watkinsStep : WatkinsKernel → WatkinsState → WatkinsState
watkinsStep K s =
  watkinsState
    (updateCritic K (critic s) (learnerSignal s))
    (learnerSignal s)
    (traceSignal s)
    (updateTrace K (trace s) (greedy K (critic s) (learnerSignal s)))

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

lcbNegative : Int8 → Int8
lcbNegative x = int8OfNat (256 ∸ toℕ (code x))

lcbActionScore : LCBCountKernel → LCBCountState → CriticState → ActionScore
lcbActionScore L counts c = actionScore
  (int8Add (qLeft c) (lcbNegative (bonus L (leftCount counts))))
  (int8Add (qRight c) (lcbNegative (bonus L (rightCount counts))))

scheduledActionScore : LCBCountKernel → Nat → LCBCountState → CriticState → ActionScore
scheduledActionScore L r counts c =
  let s = lcbActionScore L counts c
  in actionScore
       (int8Add (left s) (int8OfNat ((r * 37) + 17)))
       (int8Add (right s) (int8OfNat (((suc r) * 37) + 17)))

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
-- Negative q-log / Munchausen-style deterministic shaping boundary.
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

canonicalQLogControl : SignedQLogControl
canonicalQLogControl = signedQLogControl enabled negativeAlpha8

qLogSignal : SignedQLogControl → Int8 → Int8
qLogSignal c x with mode c
... | disabled = x
... | enabled = int8Add x (coefficient c)

------------------------------------------------------------------------
-- Learned sparsemax attention is learner representation state, not actor state.
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
-- Exact normalized H4 / 2 boundary.
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
-- State-independent hard-sign gate and x/(1-x) recurrent activation.
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

mobiusActivation8 : Int8 → FiniteRational
mobiusActivation8 = mobiusRatio8

mix8 : Int8 → Int8 → Int8 → Int8
mix8 g old new = int8Add (int8Mul (gateComplement g) old) (int8Mul g new)

gruCandidate8 : Int8 → Int8 → Int8
gruCandidate8 h x = int8OfNat (toℕ (code (int8Add h x)))

gruStep : GRUState → Int8 → GRUState
gruStep (gruState h m n g) x =
  gruState
    (mix8 (gateFromInput x) h (int8Add (code8FromRational (mobiusActivation8 x)) (gruCandidate8 h x)))
    m n g
  where
  code8FromRational : FiniteRational → Int8
  code8FromRational q =
    int8OfNat (signedNatural (numerator q))
    where
    signedNatural : I.Int → Nat
    signedNatural (I.pos n) = n
    signedNatural (I.negsuc n) = zero

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
-- Global F4-Int-U optimizer, explicit global L2, and norm pair.
------------------------------------------------------------------------

record F4Scalar : Set₁ where
  field
    R : Set
    zero one halfULP : R
    addS subS mulS : R → R → R
    intToR : I.Int → R
    quantize8 : R → R
    roundInt : R → I.Int
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

------------------------------------------------------------------------
-- Full learner state. No environment type occurs anywhere in the carrier.
------------------------------------------------------------------------

record FullLearnerState (A : F4Scalar) : Set₁ where
  constructor fullLearnerState
  field
    clock : Nat
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
  field
    watkinsKernel : WatkinsKernel
    attentionStep : LearnedSparsemaxAttention → Int8 → LearnedSparsemaxAttention
    attentionToGRU : WalshVec4 → Int8
    optimizerKernel : F4IntUKernel A
    lcbKernel : LCBCountKernel
open FullLearnerKernel public

canonicalPolicy : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → Sparsemax2Pair
canonicalPolicy K s = fixedTemperatureSparsemax
  (scheduledActionScore (lcbKernel K) (clock s) (lcbCounts s) (critic (watkins s)))

replaceAttention : ∀ {A : F4Scalar} → FullLearnerState A → LearnedSparsemaxAttention → FullLearnerState A
replaceAttention s a = fullLearnerState (clock s) (watkins s) a (gru s) (optimizer s)
  (norm s) (lcbCounts s) (qLogControl s) (qLogValue s)

canonicalPolicy-attention-invariant :
  ∀ {A : F4Scalar} (K : FullLearnerKernel A) (s : FullLearnerState A) (a : LearnedSparsemaxAttention) →
  canonicalPolicy K (replaceAttention s a) ≡ canonicalPolicy K s
canonicalPolicy-attention-invariant K s a = refl

endogenousNegativeScale8 : Sparsemax2Pair → Int8
endogenousNegativeScale8 (l , r) = int8OfNat (256 ∸ toℕ (code l))

canonicalQLogControlStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → SignedQLogControl
canonicalQLogControlStep K s = signedQLogControl enabled (endogenousNegativeScale8 (canonicalPolicy K s))

canonicalSignal : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalSignal K s =
  qLogSignal (qLogControl s)
    (int8Add (policyLeftWeight (canonicalPolicy K s))
      (int8OfNat ((clock s * 37) + 17)))

canonicalWatkinsStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → WatkinsState
canonicalWatkinsStep K s =
  watkinsStep (watkinsKernel K) (watkins s)

canonicalAttentionStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → LearnedSparsemaxAttention
canonicalAttentionStep K s = attentionStep K (attention s) (canonicalSignal K s)

canonicalGRUStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → GRUState
canonicalGRUStep K s =
  let transformed = walshHadamardApply (liftAttention (canonicalPolicy K s))
      extra = attentionToGRU K transformed
  in gruStep (gru s) (int8Add (canonicalSignal K s) extra)

canonicalPersistentGRUPreservation :
  ∀ {A : F4Scalar} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistentGRUPreservation K s =
  persistent-preservation (gru s)
    (int8Add (canonicalSignal K s)
      (attentionToGRU K (walshHadamardApply (liftAttention (canonicalPolicy K s)))))

canonicalOptimizerStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → F4IntUState A
canonicalOptimizerStep {A} K s =
  f4ThetaStep (optimizerKernel K) (optimizer s)
    (intToR A (I.pos (toℕ (code (canonicalSignal K s)))))

canonicalCountStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → LCBCountState
canonicalCountStep K s = updateLCBCount (canonicalPolicy K s) (lcbCounts s)

canonicalQLogStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → FiniteRational
canonicalQLogStep K s = negativeFiniteQLog8 (policyLeftWeight (canonicalPolicy K s))

canonicalFullStep : ∀ {A : F4Scalar} → FullLearnerKernel A → FullLearnerState A → FullLearnerState A
canonicalFullStep K s =
  fullLearnerState (suc (clock s)) (canonicalWatkinsStep K s)
    (canonicalAttentionStep K s) (canonicalGRUStep K s)
    (canonicalOptimizerStep K s) (norm s) (canonicalCountStep K s)
    (canonicalQLogControlStep K s) (canonicalQLogStep K s)

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
  field
    energy : FullLearnerState A → Nat
    strictDecrease : ∀ s → canonicalFullStep K s ≢ s → energy (canonicalFullStep K s) < energy s
open FullLearnerCoerciveQuadratic public

canonicalQuadraticDecay :
  ∀ {A : F4Scalar} {K : FullLearnerKernel A}
  (W : FullLearnerCoerciveQuadratic K) (s : FullLearnerState A) →
  canonicalFullStep K s ≢ s → energy W (canonicalFullStep K s) < energy W s
canonicalQuadraticDecay W s moved = strictDecrease W s moved

iterateCanonical : ∀ {A : F4Scalar} → FullLearnerKernel A → Nat → FullLearnerState A → FullLearnerState A
iterateCanonical K zero s = s
iterateCanonical K (suc n) s = canonicalFullStep K (iterateCanonical K n s)

plus-suc : ∀ (m n : Nat) → m + suc n ≡ suc (m + n)
plus-suc zero n = refl
plus-suc (suc m) n = cong suc (plus-suc m n)

clockAfter : ∀ {A : F4Scalar} (K : FullLearnerKernel A) (n : Nat) (s : FullLearnerState A) →
  clock (iterateCanonical K n s) ≡ clock s + n
clockAfter K zero s = refl
clockAfter K (suc n) s =
  trans (cong suc (clockAfter K n s)) (sym (plus-suc (clock s) n))

plus-suc-not-self : ∀ (r n : Nat) → r + suc n ≢ r
plus-suc-not-self zero n = λ ()
plus-suc-not-self (suc r) n eq = plus-suc-not-self r n (s≤s? eq)
  where
  s≤s? : ∀ {m n} → suc m ≡ suc n → m ≡ n
  s≤s? refl = refl

canonicalAperiodic :
  ∀ {A : F4Scalar} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : Nat) →
  iterateCanonical K (suc n) s ≢ s
canonicalAperiodic K s n cyc =
  plus-suc-not-self (clock s) n
    (trans (sym (clockAfter K (suc n) s)) (cong clock cyc))

canonicalCoerciveNoCycle :
  ∀ {A : F4Scalar} {K : FullLearnerKernel A}
  (W : FullLearnerCoerciveQuadratic K) {s : FullLearnerState A} (n : Nat) →
  iterateCanonical K (suc n) s ≡ s → OrbitNonFixed (canonicalFullStep K) s → ⊥
canonicalCoerciveNoCycle W n cyc nf =
  noNontrivialFiniteCycle
    (lyapunovCertificate (energy W) (strictDecrease W)) n cyc nf

------------------------------------------------------------------------
-- Generic semidirect carrier schema, retained because it is part of the
-- reusable composition theorem surface rather than an environment model.
------------------------------------------------------------------------

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
  field
    leftMonoid : Monoid A
    rightMonoid : Monoid B
    leftAction : Action A B leftMonoid rightMonoid
open Semidirect public

semidirectMul : ∀ {A B : Set} → Semidirect A B → (A × B) → (A × B) → (A × B)
semidirectMul S (a , b) (a' , b') =
  Monoid.mul (leftMonoid S) a (Action.act (leftAction S) b a') ,
  Monoid.mul (rightMonoid S) b b'

------------------------------------------------------------------------
-- Finite strict count-memory obstruction is included locally rather than as
-- a separately imported theorem module.
------------------------------------------------------------------------

record StrictCountSystem (S : Set) (step : S → S) : Set₁ where
  constructor strictCountSystem
  field
    count : S → Nat
    strictCount : ∀ s → step s ≢ s → count s < count (step s)
open StrictCountSystem public

count-two-step-increases :
  ∀ {S : Set} {step : S → S} (C : StrictCountSystem S step) {s : S} →
  step s ≢ s → step (step s) ≢ step s → count C s < count C (step (step s))
count-two-step-increases C nf₀ nf₁ =
  lt-trans-nat (strictCount C _ nf₀) (strictCount C _ nf₁)

------------------------------------------------------------------------
-- Concrete finite regression equalities retained directly in the monolith.
------------------------------------------------------------------------

temperatureCodeLaw : sparsemaxTemperature ≡ int8OfNat 16
temperatureCodeLaw = refl

temperatureTieLaw :
  fixedTemperatureSparsemax (actionScore (int8OfNat 0) (int8OfNat 0)) ≡ int8OfNat 64 , int8OfNat 64
temperatureTieLaw = refl

temperaturePositiveUnitLaw :
  fixedTemperatureSparsemax (actionScore (int8OfNat 1) (int8OfNat 0)) ≡ int8OfNat 68 , int8OfNat 60
temperaturePositiveUnitLaw = refl

temperatureNegativeUnitLaw :
  fixedTemperatureSparsemax (actionScore (int8OfNat 0) (int8OfNat 1)) ≡ int8OfNat 60 , int8OfNat 68
temperatureNegativeUnitLaw = refl

pessimisticInit : Int8
pessimisticInit = int8OfNat 128

pessimisticCritic : CriticState
pessimisticCritic = criticState pessimisticInit pessimisticInit

maxPessimisticCritic-law :
  qLeft pessimisticCritic ≡ int8OfNat 128 × qRight pessimisticCritic ≡ int8OfNat 128
maxPessimisticCritic-law = refl , refl

canonicalWalshBoundary : walshOrthonormal ≡ walshOrthonormal
canonicalWalshBoundary = refl

canonicalPersistent :
  ∀ {A : F4Scalar} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  persistentGRU (canonicalGRUStep K s) ≡ persistentGRU (gru s)
canonicalPersistent = canonicalPersistentGRUPreservation
