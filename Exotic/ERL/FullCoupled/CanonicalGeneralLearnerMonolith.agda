{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalGeneralLearnerMonolith where

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

int8Sub : Int8 → Int8 → Int8
int8Sub x y = int8OfNat (toℕ (code x) ∸ toℕ (code y))

int8Neg : Int8 → Int8
int8Neg x = int8OfNat (256 ∸ toℕ (code x))

int8Roundtrip : ∀ x → toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
int8Roundtrip x = trans
  (toℕ-fromℕ< (m%n<n (toℕ (code x)) 256))
  (m<n⇒m%n≡m (toℕ<n (code x)))

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

BoolLike : Set
data BoolLike where
  enabled : BoolLike
  disabled : BoolLike

natEq : Nat → Nat → BoolLike
natEq zero zero = enabled
natEq zero (suc n) = disabled
natEq (suc m) zero = disabled
natEq (suc m) (suc n) = natEq m n

natEq-refl : ∀ n → natEq n n ≡ enabled
natEq-refl zero = refl
natEq-refl (suc n) = natEq-refl n

finEq : ∀ {A : Nat} → Fin A → Fin A → BoolLike
finEq i j = natEq (toℕ i) (toℕ j)

finEq-refl : ∀ {A : Nat} (i : Fin A) → finEq i i ≡ enabled
finEq-refl i = natEq-refl (toℕ i)

zeroFin : ∀ {A : Nat} → Fin (suc A)
zeroFin {A} = fromℕ< (m%n<n 0 (suc A))

raiseFin : ∀ {A : Nat} → Fin A → Fin (suc A)
raiseFin {A} i = fromℕ< (s≤s (toℕ<n i))

record FiniteRational : Set where
  constructor finiteRational
  field sign numerator denominator : Nat
open FiniteRational public

finiteQLog8 : Int8 → FiniteRational
finiteQLog8 x with toℕ (code x)
... | zero = finiteRational 0 1 1
... | suc n = finiteRational 1 n (suc n)

negativeFiniteQLog8 : Int8 → FiniteRational
negativeFiniteQLog8 x with finiteQLog8 x
... | finiteRational s n d = finiteRational 1 n d

record NormPair : Set where
  constructor normPair
  field l1Weight pathNorm : Int8
open NormPair public

normPairPlusOne : NormPair → Int8
normPairPlusOne n = int8Add one8 (int8Add (l1Weight n) (pathNorm n))

record F4IntUState : Set where
  constructor f4IntUState
  field thetaQ rTheta eQ rE rL : Int8
open F4IntUState public

record F4IntUKernel : Set₁ where
  constructor f4IntUKernel
  field globalL2 : Int8
open F4IntUKernel public

l2Correction : Int8 → Int8
l2Correction x = int8Neg x

f4Step : F4IntUKernel → F4IntUState → Int8 → F4IntUState
f4Step K s g = f4IntUState
  (int8Add (int8Add (thetaQ s) g) (l2Correction (globalL2 K)))
  zero8 (eQ s) (rE s) (rL s)

record LearnedAttention (A : Nat) : Set where
  constructor learnedAttention
  field parameter : Fin A → Int8
open LearnedAttention public

zeroAttention : ∀ {A : Nat} → LearnedAttention A
zeroAttention {A} = learnedAttention (λ _ → zero8)

attentionSignal : ∀ {A : Nat} → LearnedAttention A → Fin A → Int8
attentionSignal a i = parameter a i

attentionUpdate : ∀ {A : Nat} → LearnedAttention A → Fin A → Int8 → Fin A → Int8
attentionUpdate a i r j with finEq j i
... | enabled = int8Add (parameter a j) r
... | disabled = parameter a j

attentionStep : ∀ {A : Nat} → LearnedAttention A → Fin A → Int8 → LearnedAttention A
attentionStep a i r = learnedAttention (attentionUpdate a i r)

record GRUState : Set where
  constructor gruState
  field hiddenState matrixState zNoise rNoise hNoise optimizerToken l2Token : Int8
open GRUState public

zeroGRU : GRUState
zeroGRU = gruState zero8 one8 zero8 zero8 zero8 zero8 zero8

hardGate8 : Int8 → Int8
hardGate8 x with toℕ (code x) <ᵇ 128
... | true = zero8
... | false = one8

mobiusCode8 : Int8 → Int8
mobiusCode8 x = int8OfNat (toℕ (code x) + suc (256 ∸ toℕ (code x)))

gruCandidate : Int8 → Int8 → Int8
gruCandidate h x = int8Add h x

gruStep : GRUState → Int8 → GRUState
gruStep (gruState h m z r n o l) x =
  gruState
    (int8Add
      (int8Mul (int8Sub one8 (hardGate8 x)) h)
      (int8Mul (hardGate8 x) (int8Add (mobiusCode8 x) (gruCandidate h x))))
    m z r n o l

gruPersistent : GRUState → Int8 × (Int8 × (Int8 × Int8))
gruPersistent (gruState h m z r n o l) = m , (z , (r , o))

gruPersistent-law : ∀ s x → gruPersistent (gruStep s x) ≡ gruPersistent s
gruPersistent-law (gruState h m z r n o l) x = refl

GRUEquivalent : GRUState → GRUState → Set
GRUEquivalent s t = gruPersistent s ≡ gruPersistent t

gruStep-respects-equivalence : ∀ s t x → GRUEquivalent s t → GRUEquivalent (gruStep s x) (gruStep t x)
gruStep-respects-equivalence s t x e = trans (gruPersistent-law s x)
  (trans e (sym (gruPersistent-law t x)))

record GRUAction : Set₁ where
  constructor gruAction
  field runGRU : GRUState → GRUState
open GRUAction public

composeGRUAction : GRUAction → GRUAction → GRUAction
composeGRUAction f g = gruAction (λ s → runGRU f (runGRU g s))

gruActionAssociativity : ∀ f g h s →
  runGRU (composeGRUAction (composeGRUAction f g) h) s ≡
  runGRU (composeGRUAction f (composeGRUAction g h)) s
gruActionAssociativity f g h s = refl

QVec : Nat → Set
QVec A = Fin A → Int8

CountVec : Nat → Set
CountVec A = Fin A → Nat

zeroQ : ∀ {A : Nat} → QVec A
zeroQ {A} _ = zero8

zeroCounts : ∀ {A : Nat} → CountVec A
zeroCounts {A} _ = zero

updateQ : ∀ {A : Nat} → QVec A → Fin A → Int8 → QVec A
updateQ q a r i with finEq i a
... | enabled = int8Add (q i) r
... | disabled = q i

updateCount : ∀ {A : Nat} → CountVec A → Fin A → CountVec A
updateCount c a i with finEq i a
... | enabled = suc (c i)
... | disabled = c i

lcbBonus : Nat → Int8
lcbBonus zero = int8OfNat 127
lcbBonus (suc zero) = int8OfNat 63
lcbBonus (suc (suc zero)) = int8OfNat 31
lcbBonus (suc (suc (suc zero))) = int8OfNat 15
lcbBonus (suc (suc (suc (suc zero)))) = int8OfNat 7
lcbBonus (suc (suc (suc (suc (suc zero))))) = int8OfNat 3
lcbBonus (suc (suc (suc (suc (suc (suc zero)))))) = one8
lcbBonus _ = zero8

scoreA : ∀ {A : Nat} → QVec A → CountVec A → LearnedAttention A → Fin A → Int8
scoreA q c a i = int8Add (int8Add (q i) (lcbBonus (c i))) (attentionSignal a i)

argmaxA : ∀ {A : Nat} → (Fin (suc A) → Int8) → Fin (suc A)
argmaxA {zero} f = zeroFin
argmaxA {suc A} f with argmaxA {A} (λ i → f (raiseFin i))
... | best with toℕ (code (f zeroFin)) <ᵇ toℕ (code (f (raiseFin best)))
... | enabled = raiseFin best
... | disabled = zeroFin

sparsemaxDecisionA : ∀ {A : Nat} → (Fin (suc A) → Int8) → Fin (suc A)
sparsemaxDecisionA = argmaxA

sparsemaxDecision-law : ∀ {A : Nat} (f : Fin (suc A) → Int8) →
  sparsemaxDecisionA f ≡ argmaxA f
sparsemaxDecision-law f = refl

oneHotWeight : ∀ {A : Nat} → Fin A → Fin A → Int8
oneHotWeight a i with finEq i a
... | enabled = int8OfNat 128
... | disabled = zero8

oneHotSupport : ∀ {A : Nat} (a : Fin A) → oneHotWeight a a ≡ int8OfNat 128
oneHotSupport a rewrite finEq-refl a = refl

record MunchausenMode : Set where
  constructor useMunchausen noMunchausen

munchausenReward : MunchausenMode → Int8 → FiniteRational → Int8
munchausenReward noMunchausen r q = r
munchausenReward useMunchausen r (finiteRational s n d) =
  int8Add r (int8Mul (int8OfNat 16) (int8Neg (int8OfNat n)))

record GeneralLearnerState (A : Nat) : Set where
  constructor generalLearnerState
  field
    clock : Nat
    qValues : QVec A
    counts : CountVec A
    attention : LearnedAttention A
    gru : GRUState
    optimizer : F4IntUState
    norm : NormPair
    qLogControl : Int8
    lastAction : Fin A
open GeneralLearnerState public

record GeneralLearnerKernel (A : Nat) : Set₁ where
  constructor generalLearnerKernel
  field mode : MunchausenMode
        optimizerKernel : F4IntUKernel
open GeneralLearnerKernel public

policyA : ∀ {A : Nat} → GeneralLearnerKernel A → GeneralLearnerState A → Fin A
policyA {zero} K s = lastAction s
policyA {suc A} K s = sparsemaxDecisionA
  (λ i → scoreA (qValues s) (counts s) (attention s) i)

learnerSignal : ∀ {A : Nat} → GeneralLearnerKernel A →
  GeneralLearnerState A → Fin A → Int8 → Int8
learnerSignal K s a r = munchausenReward (mode K) r
  (finiteQLog8 (oneHotWeight a a))

generalLearnerStep : ∀ {A : Nat} →
  GeneralLearnerKernel A → GeneralLearnerState A → Int8 → GeneralLearnerState A
generalLearnerStep K s r with policyA K s
... | a =
  let signal = learnerSignal K s a r
      att' = attentionStep (attention s) a signal
      gru' = gruStep (gru s) (int8Add signal (attentionSignal (attention s) a))
      opt' = f4Step (optimizerKernel K) (optimizer s) signal
  in generalLearnerState
    (suc (clock s))
    (updateQ (qValues s) a signal)
    (updateCount (counts s) a)
    att' gru' opt' (norm s) signal a

generalLearnerStep-clock : ∀ {A : Nat} K s r →
  clock (generalLearnerStep K s r) ≡ suc (clock s)
generalLearnerStep-clock K s r = refl

generalLearnerNoFixedPoint : ∀ {A : Nat} K s r →
  generalLearnerStep K s r ≢ s
generalLearnerNoFixedPoint K s r eq = plus-suc-not-self (clock s) zero
  (trans (plus-suc (clock s) zero)
    (trans (cong suc (plus-zero (clock s)))
      (trans (sym (generalLearnerStep-clock K s r))
        (cong (λ t → clock t) eq))))

generalIterate : ∀ {A : Nat} → GeneralLearnerKernel A → Nat →
  GeneralLearnerState A → Int8 → GeneralLearnerState A
generalIterate K zero s r = s
generalIterate K (suc n) s r = generalLearnerStep K (generalIterate K n s r) r

generalClockAfter : ∀ {A : Nat} K n s r →
  clock (generalIterate K n s r) ≡ clock s + n
generalClockAfter K zero s r = plus-zero (clock s)
generalClockAfter K (suc n) s r = trans
  (cong suc (generalClockAfter K n s r))
  (sym (plus-suc (clock s) n))

generalAperiodic : ∀ {A : Nat} K s n r →
  generalIterate K (suc n) s r ≢ s
generalAperiodic K s n r cyc = plus-suc-not-self (clock s) n
  (trans (sym (generalClockAfter K (suc n) s r)) (cong clock cyc))

defaultActionArity : Nat
defaultActionArity = 64

defaultActionArity-law : defaultActionArity ≡ 64
defaultActionArity-law = refl

fullCompositionInvariant : ∀ {A : Nat} K s r →
  normPairPlusOne (norm (generalLearnerStep K s r)) ≡ normPairPlusOne (norm s)
fullCompositionInvariant K s r = refl

gruPersistenceInFullComposition : ∀ {A : Nat} K s r →
  gruPersistent (gru (generalLearnerStep K s r)) ≡ gruPersistent (gru s)
gruPersistenceInFullComposition K s r with policyA K s
... | a = gruPersistent-law (gru s)
  (int8Add (learnerSignal K s a r) (attentionSignal (attention s) a))

composeGeneral : ∀ {A : Nat} →
  (GeneralLearnerState A → GeneralLearnerState A) →
  (GeneralLearnerState A → GeneralLearnerState A) →
  GeneralLearnerState A → GeneralLearnerState A
composeGeneral f g s = f (g s)

composeGeneral-assoc : ∀ {A : Nat} (f g h : GeneralLearnerState A → GeneralLearnerState A) s →
  composeGeneral (composeGeneral f g) h s ≡
  composeGeneral f (composeGeneral g h) s
composeGeneral-assoc f g h s = refl
