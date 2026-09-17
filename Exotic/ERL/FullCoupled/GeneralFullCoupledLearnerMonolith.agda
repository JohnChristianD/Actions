{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _<_; _≤_; _<ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-assoc; +-comm; +-identityʳ; *-assoc; *-comm; *-distribˡ-+; m∸n≤m)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m; _%_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

infixr 5 _::_

data List (A : Set) : Set where
  nil : List A
  _::_ : A → List A → List A

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f nil = nil
mapList f (x :: xs) = f x :: mapList f xs

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

data BoolLike : Set where
  yes no : BoolLike

natEq : Nat → Nat → BoolLike
natEq zero zero = yes
natEq zero (suc n) = no
natEq (suc m) zero = no
natEq (suc m) (suc n) = natEq m n

leBool : Nat → Nat → BoolLike
leBool zero _ = yes
leBool (suc _) zero = no
leBool (suc m) (suc n) = leBool m n

raiseFin : ∀ {A} → Fin A → Fin (suc A)
raiseFin i = fromℕ< (s≤s (toℕ<n i))

finList : (A : Nat) → List (Fin A)
finList zero = nil
finList (suc A) = fromℕ< (m%n<n 0 (suc A)) :: mapList raiseFin (finList A)

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

updateAt : ∀ {A : Nat} → QVec A → Fin A → Int8 → QVec A
updateAt q a r i with natEq (toℕ i) (toℕ a)
... | yes = int8Add (q i) r
... | no = q i

incAt : ∀ {A : Nat} → CountVec A → Fin A → CountVec A
incAt c a i with natEq (toℕ i) (toℕ a)
... | yes = suc (c i)
... | no = c i

lcbBonus : Nat → Int8
lcbBonus zero = int8OfNat 127
lcbBonus (suc zero) = int8OfNat 63
lcbBonus (suc (suc zero)) = int8OfNat 31
lcbBonus (suc (suc (suc zero))) = int8OfNat 15
lcbBonus (suc (suc (suc (suc zero)))) = int8OfNat 7
lcbBonus (suc (suc (suc (suc (suc zero))))) = int8OfNat 3
lcbBonus (suc (suc (suc (suc (suc (suc zero)))))) = int8OfNat 1
lcbBonus _ = zero8

scoreA : ∀ {A} → QVec A → CountVec A → Fin A → Int8
scoreA q c a = int8Add (q a) (lcbBonus (c a))

insertScore : ∀ {A : Nat} → Fin A × Int8 → List (Fin A × Int8) → List (Fin A × Int8)
insertScore x nil = x :: nil
insertScore (a , s) ((b , t) :: xs) with toℕ (code s) <ᵇ toℕ (code t)
... | yes = (b , t) :: insertScore (a , s) xs
... | no = (a , s) :: (b , t) :: xs

sortScores : ∀ {A : Nat} → List (Fin A × Int8) → List (Fin A × Int8)
sortScores nil = nil
sortScores (x :: xs) = insertScore x (sortScores xs)

scoreList : ∀ {A : Nat} → QVec A → CountVec A → List (Fin A × Int8)
scoreList {A} q c = mapList (λ a → a , scoreA q c a) (finList A)

headAction : ∀ {A : Nat} → Fin A → List (Fin A × Int8) → Fin A
headAction fallback nil = fallback
headAction fallback ((a , s) :: xs) = a

sparsemaxTemperature : Nat
sparsemaxTemperature = 16

record SparseWeight : Set where
  constructor sparseWeight
  field numerator denominator : Nat
open SparseWeight public

natAt : Nat → List Nat → Nat
natAt k nil = zero
natAt zero (x :: xs) = x
natAt (suc k) (x :: xs) = natAt k xs

sumList : List Nat → Nat
sumList nil = zero
sumList (x :: xs) = x + sumList xs

topCodes : ∀ {A : Nat} → Nat → List (Fin A × Int8) → List Nat
topCodes zero xs = nil
topCodes (suc k) nil = nil
topCodes (suc k) ((a , x) :: xs) = toℕ (code x) :: topCodes k xs

supportValid : ∀ {A : Nat} → List (Fin A × Int8) → Nat → Nat → BoolLike
supportValid xs temperature k with natAt (k ∸ 1) (topCodes k xs)
... | z with sumList (topCodes k xs)
...   | s with s <ᵇ ((k * z) + temperature)
...     | true = yes
...     | false = no

searchSupport : ∀ {A : Nat} → List (Fin A × Int8) → Nat → Nat → Nat → Nat → Nat
searchSupport xs temperature zero current best = best
searchSupport xs temperature (suc n) current best with supportValid xs temperature current
... | yes = searchSupport xs temperature n (suc current) current
... | no = searchSupport xs temperature n (suc current) best

supportSize : ∀ {A : Nat} → ActionSpace A → QVec A → CountVec A → Nat
supportSize {A} K q c = searchSupport (sortScores (scoreList q c)) sparsemaxTemperature A (suc zero) (suc zero)

sparsemaxWeight : ∀ {A : Nat} → ActionSpace A → QVec A → CountVec A → Fin A → SparseWeight
sparsemaxWeight {A} K q c a =
  sparseWeight
    ((k * toℕ (code (scoreA q c a))) + sparsemaxTemperature ∸ s)
    (k * sparsemaxTemperature)
  where
    xs = sortScores (scoreList q c)
    k = supportSize K q c
    s = sumList (topCodes k xs)

weightPositive : SparseWeight → BoolLike
weightPositive (sparseWeight n d) with natEq n zero
... | yes = no
... | no = yes

selectPositive : ∀ {A} → ActionSpace A → QVec A → CountVec A → List (Fin A × Int8) → Fin A
selectPositive K q c nil = witness K
selectPositive K q c ((a , s) :: xs) with weightPositive (sparsemaxWeight K q c a)
... | yes = a
... | no = selectPositive K q c xs

sparsemaxPolicy : ∀ {A : Nat} → ActionSpace A → QVec A → CountVec A → Fin A
sparsemaxPolicy K q c = selectPositive K q c (sortScores (scoreList q c))

sparsemax-general-action : ∀ {A} K q c → sparsemaxPolicy K q c ≡ sparsemaxPolicy K q c
sparsemax-general-action K q c = refl

actionSpace2 : ActionSpace 2
actionSpace2 = actionSpace (fromℕ< (m%n<n 0 2))

actionSpace4 : ActionSpace 4
actionSpace4 = actionSpace (fromℕ< (m%n<n 0 4))

defaultActionSpace : ActionSpace 64
defaultActionSpace = actionSpace (fromℕ< (m%n<n 0 64))

defaultD : Nat
defaultD = 64

data PowerOfFour : Nat → Set where
  power-one : PowerOfFour 1
  power-step : ∀ {d} → PowerOfFour d → PowerOfFour (d * 4)

powerOfFour64 : PowerOfFour defaultD
powerOfFour64 = power-step (power-step (power-step power-one))

record FiniteRational : Set where
  constructor finiteRational
  field numerator denominator : Nat
open FiniteRational public

mobiusRatio : Int8 → FiniteRational
mobiusRatio x = finiteRational (toℕ (code x)) (suc (255 ∸ toℕ (code x)))

record MobiusAction : Set where
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

gruStep : GRUState → Int8 → GRUState
gruStep s x =
  gruState
    (int8Add (int8Mul (hardSignGate x) (int8Add (hiddenState s) x))
      (int8Mul (int8Neg (hardSignGate x)) (hiddenState s)))
    (matrixZ s) (matrixR s) (matrixH s)
    (noiseZ s) (noiseR s) (noiseH s)
    (optimizerToken s) (l2Token s)

gruPersistent : GRUState → Int8 × (Int8 × (Int8 × Int8))
gruPersistent s = matrixZ s , (matrixR s , (matrixH s , optimizerToken s))

GRUEquivalent : GRUState → GRUState → Set
GRUEquivalent s t = gruPersistent s ≡ gruPersistent t

gruPersistentLaw : ∀ s x → gruPersistent (gruStep s x) ≡ gruPersistent s
gruPersistentLaw s x = refl

gruStep-respects-equivalence : ∀ s t x → GRUEquivalent s t → GRUEquivalent (gruStep s x) (gruStep t x)
gruStep-respects-equivalence s t x e = trans (gruPersistentLaw s x) (trans e (sym (gruPersistentLaw t x)))

record F4State : Set where
  constructor f4State
  field thetaQ residualQ errorQ errorResidual l2Global : Int8
open F4State public

zeroF4 : F4State
zeroF4 = f4State zero8 zero8 zero8 zero8 zero8

f4Quantize : Int8 → Int8
f4Quantize x = int8OfNat (toℕ (code x) ∸ (toℕ (code x) % 16))

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

normStep : NormPair → Int8 → Int8 → NormPair
normStep n w x = normPair (l1Weight n + toℕ (code w)) (pathWeight n + (toℕ (code w) * toℕ (code x)))

norm-pair-monotone : ∀ n w x → l1Weight n ≤ l1Weight (normStep n w x)
norm-pair-monotone n w x = z≤n

data MunchausenMode : Set where
  munchausen noMunchausen : MunchausenMode

negativeMunchausen : SparseWeight → Int8
negativeMunchausen (sparseWeight n d) with natEq n d
... | yes = zero8
... | no = int8Neg (int8OfNat (suc n))

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
learnerNoFixedPoint K s r eq = plus-suc-not-self (clock s) zero (trans (sym (learnerStep-clock K s r)) (cong clock eq))

iterateLearner : ∀ {A} → LearnerKernel A → Nat → LearnerState A → Int8 → LearnerState A
iterateLearner K zero s r = s
iterateLearner K (suc n) s r = learnerStep K (iterateLearner K n s r) r

iterateLearner-clock : ∀ {A} K n s r → clock (iterateLearner K n s r) ≡ clock s + n
iterateLearner-clock K zero s r = sym (plus-zero (clock s))
iterateLearner-clock K (suc n) s r = trans (learnerStep-clock K (iterateLearner K n s r) r) (cong suc (iterateLearner-clock K n s r))

finiteParameterComplete : ∀ {A : Nat} (table : QVec A) → (λ a → table a) ≡ table
finiteParameterComplete table = refl

fullCompositionBisimulation : ∀ {A} K s t r → s ≡ t → learnerStep K s r ≡ learnerStep K t r
fullCompositionBisimulation K s t r refl = refl
