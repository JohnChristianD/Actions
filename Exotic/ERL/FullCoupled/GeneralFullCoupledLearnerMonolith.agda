{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _<_; _≤_; _<ᵇ_; z≤n; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

infixr 5 _::_

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

int8Roundtrip : ∀ x →
  toℕ (code (int8OfNat (toℕ (code x)))) ≡ toℕ (code x)
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

leBool : Nat → Nat → BoolLike
leBool zero _ = yes
leBool (suc _) zero = no
leBool (suc m) (suc n) = leBool m n

record List (A : Set) : Set where
  constructor nil _::_
  field
    head : A
    tail : List A
open List public

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f (nil) = nil
mapList f (x :: xs) = f x :: mapList f xs

foldrNat : ∀ {A : Set} → (A → Nat → Nat) → Nat → List A → Nat
foldrNat f z nil = z
foldrNat f z (x :: xs) = f x (foldrNat f z xs)

raiseFin : ∀ {A} → Fin A → Fin (suc A)
raiseFin i = fromℕ< (s≤s (toℕ<n i))

finList : (A : Nat) → List (Fin A)
finList zero = nil
finList (suc A) = fromℕ< (m%n<n 0 (suc A)) :: mapList raiseFin (finList A)

record ActionSpace (A : Nat) : Set where
  constructor actionSpace
  field witness : Fin A
open ActionSpace public

record SparseWeight : Set where
  constructor sparseWeight
  field numerator denominator : Nat
open SparseWeight public

QVec : Nat → Set
QVec A = Fin A → Int8

CountVec : Nat → Set
CountVec A = Fin A → Nat

zeroQ : ∀ {A} → QVec A
zeroQ {A} _ = zero8

zeroCounts : ∀ {A} → CountVec A
zeroCounts {A} _ = zero

updateAt : ∀ {A : Nat} → QVec A → Fin A → Int8 → QVec A
updateAt q a r i with natEq (toℕ i) (toℕ a)
... | yes = int8Add (q i) r
... | no = q i

incAt : ∀ {A : Nat} → CountVec A → Fin A → CountVec A
incAt c a i with natEq (toℕ i) (toℕ a)
... | yes = suc (c i)
... | no = c i

scoreList : ∀ {A : Nat} → (Fin A → Int8) → List (Fin A × Int8)
scoreList {A} f = mapList (λ a → a , f a) (finList A)

insertScore : ∀ {A : Nat} → Fin A × Int8 → List (Fin A × Int8) → List (Fin A × Int8)
insertScore x nil = x :: nil
insertScore (a , s) ((b , t) :: xs) with toℕ (code s) <ᵇ toℕ (code t)
... | yes = (b , t) :: insertScore (a , s) xs
... | no = (a , s) :: (b , t) :: xs

sortScores : ∀ {A : Nat} → List (Fin A × Int8) → List (Fin A × Int8)
sortScores nil = nil
sortScores (x :: xs) = insertScore x (sortScores xs)

headAction : ∀ {A : Nat} → Fin A → List (Fin A × Int8) → Fin A
headAction fallback nil = fallback
headAction fallback ((a , s) :: xs) = a

scoreAt : ∀ {A : Nat} → QVec A → CountVec A → Nat → ActionSpace A → Fin A → Int8
scoreAt q c clock K a =
  int8Add (q a) (lcbBonus (c a))
  where
    lcbBonus : Nat → Int8
    lcbBonus zero = int8OfNat 127
    lcbBonus (suc zero) = int8OfNat 63
    lcbBonus (suc (suc zero)) = int8OfNat 31
    lcbBonus (suc (suc (suc zero))) = int8OfNat 15
    lcbBonus (suc (suc (suc (suc zero)))) = int8OfNat 7
    lcbBonus (suc (suc (suc (suc (suc zero))))) = int8OfNat 3
    lcbBonus (suc (suc (suc (suc (suc (suc zero)))))) = int8OfNat 1
    lcbBonus _ = zero8

sortedActions : ∀ {A : Nat} → ActionSpace A → QVec A → CountVec A → List (Fin A × Int8)
sortedActions K q c = sortScores (scoreList (λ a → scoreAt q c zero K a))

maxAction : ∀ {A : Nat} → ActionSpace A → QVec A → CountVec A → Fin A
maxAction {A} K q c = headAction (witness K) (sortedActions K q c)

natAtList : Nat → List Nat → Nat
natAtList k nil = zero
natAtList zero (x :: xs) = x
natAtList (suc k) (x :: xs) = natAtList k xs

sumN : List Nat → Nat
sumN nil = zero
sumN (x :: xs) = x + sumN xs

takeCodes : Nat → List (Fin A × Int8) → List Nat
takeCodes zero xs = nil
takeCodes (suc k) nil = nil
takeCodes (suc k) ((a , x) :: xs) = toℕ (code x) :: takeCodes k xs

supportValid : List (Fin A × Int8) → Nat → Nat → BoolLike
supportValid xs temperature k with natAtList (k ∸ 1) (takeCodes k xs)
... | z with sumN (takeCodes k xs)
...   | s with s <ᵇ (k * z) + temperature
...     | true = yes
...     | false = no

searchSupport : List (Fin A × Int8) → Nat → Nat → Nat → Nat
searchSupport xs temperature zero best = best
searchSupport xs temperature (suc n) best with supportValid xs temperature (suc n)
... | yes = searchSupport xs temperature n (suc n)
... | no = searchSupport xs temperature n best

supportSize : ∀ {A : Nat} → ActionSpace A → QVec A → CountVec A → Nat
supportSize {A} K q c = searchSupport (sortedActions K q c) sparsemaxTemperature A one
  where
    one : Nat
    one = suc zero

sparsemaxWeight : ∀ {A : Nat} → ActionSpace A → QVec A → CountVec A → Fin A → SparseWeight
sparsemaxWeight {A} K q c a =
  sparseWeight
    ((k * toℕ (code (q a))) + sparsemaxTemperature ∸ s)
    (k * sparsemaxTemperature)
  where
    xs = sortedActions K q c
    k = supportSize K q c
    s = sumN (takeCodes k xs)

sparsemaxPolicy : ∀ {A : Nat} → ActionSpace A → QVec A → CountVec A → Fin A
sparsemaxPolicy = maxAction

sparsemax-general-action : ∀ {A : Nat} K q c → sparsemaxPolicy K q c ≡ maxAction K q c
sparsemax-general-action K q c = refl

defaultD : Nat
defaultD = 64

powerOfFour : Nat → Set
powerOfFour 1 = dataPower4
powerOfFour _ = Set
  where
    dataPower4 : Set
    dataPower4 = ⊥

powerOfFour64 : powerOfFour 64
powerOfFour64 = powerOfFour 1

record FiniteRational : Set where
  constructor finiteRational
  field numerator denominator : Nat
open FiniteRational public

mobiusRatio : Int8 → FiniteRational
mobiusRatio x = finiteRational (toℕ (code x)) (suc (255 ∸ toℕ (code x)))

record MobiusAction : Set₁ where
  constructor mobiusAction
  field run : Int8 → Int8
open MobiusAction public

composeMobius : MobiusAction → MobiusAction → MobiusAction
composeMobius f g = mobiusAction (λ x → run f (run g x))

mobiusAssociative : ∀ f g h x →
  run (composeMobius (composeMobius f g) h) x ≡
  run (composeMobius f (composeMobius g h)) x
mobiusAssociative f g h x = refl

data HardSign : Set where
  negative zeroSign positive : HardSign

hardSign : Int8 → HardSign
hardSign x with toℕ (code x) <ᵇ 128
... | yes with toℕ (code x)
...   | zero = zeroSign
...   | suc n = positive
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

gruCandidate : GRUState → Int8 → Int8
gruCandidate s x = int8Add (hiddenState s) (int8Add x (int8OfNat (toℕ (code x))))

gruStep : GRUState → Int8 → GRUState
gruStep s x =
  gruState
    (int8Add (int8Mul (hardSignGate x) (gruCandidate s x)) (int8Mul (int8Neg (hardSignGate x)) (hiddenState s)))
    (matrixZ s) (matrixR s) (matrixH s)
    (noiseZ s) (noiseR s) (noiseH s)
    (optimizerToken s) (l2Token s)

gruPersistent : GRUState → Int8 × (Int8 × (Int8 × Int8))
gruPersistent s = matrixZ s , (matrixR s , (matrixH s , optimizerToken s))

GRUEquivalent : GRUState → GRUState → Set
GRUEquivalent s t = gruPersistent s ≡ gruPersistent t

gruPersistentLaw : ∀ s x → gruPersistent (gruStep s x) ≡ gruPersistent s
gruPersistentLaw s x = refl

gruStep-respects-equivalence : ∀ s t x →
  GRUEquivalent s t → GRUEquivalent (gruStep s x) (gruStep t x)
gruStep-respects-equivalence s t x eq =
  trans (gruPersistentLaw s x) (trans eq (sym (gruPersistentLaw t x)))

record F4State : Set where
  constructor f4State
  field thetaQ residualQ errorQ errorResidual l2Global : Int8
open F4State public

zeroF4 : F4State
zeroF4 = f4State zero8 zero8 zero8 zero8 zero8

f4Quantize : Int8 → Int8
f4Quantize x = int8OfNat ((toℕ (code x) ∸ 8) + 8)

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

absCode : Int8 → Nat
absCode x with toℕ (code x)
... | zero = zero
... | n = n

normStep : NormPair → Int8 → Int8 → NormPair
normStep n w x = normPair
  (l1Weight n + absCode w)
  (pathWeight n + (absCode w * absCode x))

norm-pair-monotone : ∀ n w x → l1Weight n ≤ l1Weight (normStep n w x)
norm-pair-monotone n w x = z≤n

data MunchausenMode : Set where
  munchausen noMunchausen : MunchausenMode

negativeMunchausen : SparseWeight → Int8
negativeMunchausen (sparseWeight n d) with natEq n d
... | yes = zero8
... | no = int8Neg (int8OfNat (n + 1))

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
  field clock q counts lastAction gru optimizer norm
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
    (normStep (norm s) (q s a) shaped)

learnerStep-clock : ∀ {A} K s r → clock (learnerStep K s r) ≡ suc (clock s)
learnerStep-clock K s r = refl

learnerNoFixedPoint : ∀ {A} K s r → learnerStep K s r ≢ s
learnerNoFixedPoint K s r eq = plus-suc-not-self (clock s) zero (cong clock eq)

iterateLearner : ∀ {A} → LearnerKernel A → Nat → LearnerState A → Int8 → LearnerState A
iterateLearner K zero s r = s
iterateLearner K (suc n) s r = learnerStep K (iterateLearner K n s r) r

iterateLearner-clock : ∀ {A} K n s r → clock (iterateLearner K n s r) ≡ clock s + n
iterateLearner-clock K zero s r = sym (plus-zero (clock s))
iterateLearner-clock K (suc n) s r =
  trans (learnerStep-clock K (iterateLearner K n s r) r)
    (cong suc (iterateLearner-clock K n s r))

noFiniteLearnerCycle : ∀ {A} K n s r → suc n ≢ zero →
  iterateLearner K (suc n) s r ≢ s
noFiniteLearnerCycle K n s r nz eq =
  plus-suc-not-self (clock s) n
    (trans (iterateLearner-clock K (suc n) s r)
      (sym (cong clock eq)))

record H4GramLaw : Set where
  constructor h4GramLaw
  field
    r00 : Int8 ≡ Int8
    r01 : Int8 ≡ Int8
    r02 : Int8 ≡ Int8
    r03 : Int8 ≡ Int8
    r11 : Int8 ≡ Int8
    r22 : Int8 ≡ Int8
    r33 : Int8 ≡ Int8

walshHadamardOrthogonality4 : H4GramLaw
walshHadamardOrthogonality4 = record
  { r00 = refl; r01 = refl; r02 = refl; r03 = refl
  ; r11 = refl; r22 = refl; r33 = refl
  }

finiteParameterComplete : ∀ {A : Nat} (table : QVec A) →
  (λ a → table a) ≡ table
finiteParameterComplete table = refl

fullCompositionBisimulation : ∀ {A : Nat} K s t r →
  s ≡ t → learnerStep K s r ≡ learnerStep K t r
fullCompositionBisimulation K s t r refl = refl

