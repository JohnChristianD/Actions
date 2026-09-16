{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.GeneralActionLearnerMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
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
  yes no : BoolLike

natEq : Nat → Nat → BoolLike
natEq zero zero = yes
natEq zero (suc n) = no
natEq (suc m) zero = no
natEq (suc m) (suc n) = natEq m n

natEq-refl : ∀ n → natEq n n ≡ yes
natEq-refl zero = refl
natEq-refl (suc n) = natEq-refl n

finEq : ∀ {A : Nat} → Fin A → Fin A → BoolLike
finEq i j = natEq (toℕ i) (toℕ j)

finEq-refl : ∀ {A : Nat} (i : Fin A) → finEq i i ≡ yes
finEq-refl i = natEq-refl (toℕ i)

raiseFin : ∀ {A : Nat} → Fin A → Fin (suc A)
raiseFin {A} i = fromℕ< (s≤s (toℕ<n i))

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

mobius8 : Int8 → Int8
mobius8 x = x

gruStep : GRUState → Int8 → GRUState
gruStep (gruState h m z r n o l) x =
  gruState
    (int8Add (int8Sub one8 (hardGate8 x))
      (int8Add h (int8Add x (mobius8 x))))
    m z r n o l

gruPersistent : GRUState → Int8 × (Int8 × (Int8 × Int8))
gruPersistent (gruState h m z r n o l) = m , (z , (r , o))

gruPersistentLaw : ∀ s x → gruPersistent (gruStep s x) ≡ gruPersistent s
gruPersistentLaw (gruState h m z r n o l) x = refl

GRUEquivalent : GRUState → GRUState → Set
GRUEquivalent s t = gruPersistent s ≡ gruPersistent t

gruStepRespectsEquivalent : ∀ s t x → GRUEquivalent s t → GRUEquivalent (gruStep s x) (gruStep t x)
gruStepRespectsEquivalent s t x e = trans (gruPersistentLaw s x)
  (trans e (sym (gruPersistentLaw t x)))

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
... | yes = int8Add (q i) r
... | no = q i

updateCount : ∀ {A : Nat} → CountVec A → Fin A → CountVec A
updateCount c a i with finEq i a
... | yes = suc (c i)
... | no = c i

lcbBonus : Nat → Int8
lcbBonus zero = int8OfNat 127
lcbBonus (suc zero) = int8OfNat 63
lcbBonus (suc (suc zero)) = int8OfNat 31
lcbBonus (suc (suc (suc zero))) = int8OfNat 15
lcbBonus (suc (suc (suc (suc zero)))) = int8OfNat 7
lcbBonus (suc (suc (suc (suc (suc zero))))) = int8OfNat 3
lcbBonus (suc (suc (suc (suc (suc (suc zero)))))) = one8
lcbBonus _ = zero8

scoreA : ∀ {A : Nat} → QVec A → CountVec A → Fin A → Int8
scoreA q c a = int8Add (q a) (lcbBonus (c a))

argmaxA : ∀ {A : Nat} → Fin (suc A) → (Fin (suc A) → Int8) → Fin (suc A)
argmaxA {zero} start f = start
argmaxA {suc A} start f with argmaxA {A} (fromℕ< (m%n<n 0 (suc A))) (λ i → f (raiseFin i))
... | best with toℕ (code (f start)) <ᵇ toℕ (code (f best))
... | yes = best
... | no = start

sparsemaxExtremeA : ∀ {A : Nat} → (Fin (suc A) → Int8) → Fin (suc A)
sparsemaxExtremeA = argmaxA (fromℕ< (m%n<n 0 1))

oneHotWeightA : ∀ {A : Nat} → Fin (suc A) → Fin (suc A) → Int8
oneHotWeightA a i with finEq a i
... | yes = int8OfNat 128
... | no = zero8

oneHotSupportA : ∀ {A : Nat} (a : Fin (suc A)) → oneHotWeightA a a ≡ int8OfNat 128
oneHotSupportA a rewrite finEq-refl a = refl

record MunchausenMode : Set where
  constructor useMunchausen noMunchausen

record GeneralState (A : Nat) : Set where
  constructor generalState
  field clock : Nat
        q : QVec A
        counts : CountVec A
        gru : GRUState
        lastAction : Fin A
open GeneralState public

record GeneralKernel (A : Nat) : Set where
  constructor generalKernel
  field mode : MunchausenMode
open GeneralKernel public

munchausenSignal : MunchausenMode → Int8 → Int8
munchausenSignal useMunchausen r = int8Neg r
munchausenSignal noMunchausen r = zero8

generalPolicy : ∀ {A : Nat} → GeneralKernel A → GeneralState A → Fin A
generalPolicy {zero} K s = lastAction s
generalPolicy {suc A} K s =
  sparsemaxExtremeA (λ a → scoreA (q s) (counts s) a)

generalStep : ∀ {A : Nat} → GeneralKernel A → GeneralState A → Int8 → GeneralState A
generalStep K s r with generalPolicy K s
... | a = generalState
  (suc (clock s))
  (updateQ (q s) a (int8Add r (munchausenSignal (mode K) r)))
  (updateCount (counts s) a)
  (gruStep (gru s) (int8Add r (munchausenSignal (mode K) r)))
  a

generalStep-clock : ∀ {A : Nat} K s r → clock (generalStep K s r) ≡ suc (clock s)
generalStep-clock K s r = refl

generalNoFixedPoint : ∀ {A : Nat} K s r → generalStep K s r ≢ s
generalNoFixedPoint K s r eq = plus-suc-not-self (clock s) zero
  (trans (plus-suc (clock s) zero)
    (trans (cong suc (plus-zero (clock s)))
      (trans (sym (generalStep-clock K s r))
        (cong (λ t → clock t) eq))))

defaultActionCount : Nat
defaultActionCount = 64

defaultActionIndex : Nat
defaultActionIndex = 63

defaultActionCount-law : defaultActionCount ≡ 64
defaultActionCount-law = refl

defaultActionIndex-law : defaultActionIndex ≡ 63
defaultActionIndex-law = refl

extremeSparsemaxSupportOne : ∀ {A : Nat} (f : Fin (suc A) → Int8) →
  oneHotWeightA (sparsemaxExtremeA f) (sparsemaxExtremeA f) ≡ int8OfNat 128
extremeSparsemaxSupportOne f = oneHotSupportA (sparsemaxExtremeA f)

stepAction : ∀ {A : Nat} → GeneralKernel A → Int8 → GeneralState A → GeneralState A
stepAction K r s = generalStep K s r

composeStepAction : ∀ {A : Nat} →
  (GeneralState A → GeneralState A) →
  (GeneralState A → GeneralState A) →
  GeneralState A → GeneralState A
composeStepAction f g s = f (g s)

composeStepAssociative : ∀ {A : Nat} (f g h : GeneralState A → GeneralState A) s →
  composeStepAction (composeStepAction f g) h s ≡
  composeStepAction f (composeStepAction g h) s
composeStepAssociative f g h s = refl
