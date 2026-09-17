{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_) 
open import Level using (0ℓ)
open import Data.Nat using (_∸_; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n; ≤-decTotalOrder)
open import Data.Nat.DivMod using (m%n<n; _%_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Sort as Sort
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Binary.Construct.On as On
open import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Data.Product.Relation.Binary.Lex.NonStrict as Lex

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

data BoolLike : Set where
  yes no : BoolLike

natEq : Nat → Nat → BoolLike
natEq zero zero = yes
natEq zero (suc n) = no
natEq (suc m) zero = no
natEq (suc m) (suc n) = natEq m n

natLt : Nat → Nat → BoolLike
natLt zero zero = no
natLt zero (suc n) = yes
natLt (suc m) zero = no
natLt (suc m) (suc n) = natLt m n

maxNat : Nat → Nat → Nat
maxNat zero n = n
maxNat (suc m) zero = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

raiseFin : ∀ {A} → Fin A → Fin (suc A)
raiseFin i = fromℕ< (s≤s (toℕ<n i))

finList : (A : Nat) → List (Fin A)
finList zero = []
finList (suc A) = fromℕ< (m%n<n 0 (suc A)) ∷ map raiseFin (finList A)

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

updateAt : ∀ {A} → QVec A → Fin A → Int8 → QVec A
updateAt q a r i with natEq (toℕ i) (toℕ a)
... | yes = int8Add (q i) r
... | no = q i

incAt : ∀ {A} → CountVec A → Fin A → CountVec A
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

ScoreEntry : Nat → Set
ScoreEntry A = Int8 × Fin A

int8Order : DecTotalOrder 0ℓ 0ℓ 0ℓ
int8Order = On.decTotalOrder (≤-decTotalOrder 256) code

scoreEntryOrder : ∀ A → DecTotalOrder 0ℓ 0ℓ 0ℓ
scoreEntryOrder A =
  Flip.decTotalOrder
    (Lex.×-decTotalOrder int8Order (≤-decTotalOrder A))

scoreEntry : ∀ {A} → QVec A → CountVec A → Fin A → ScoreEntry A
scoreEntry q c a = scoreA q c a , a

scoreList : ∀ {A} → QVec A → CountVec A → List (ScoreEntry A)
scoreList {A} q c = map (scoreEntry q c) (finList A)

sortScores : ∀ {A} → List (ScoreEntry A) → List (ScoreEntry A)
sortScores {A} = Sort.sort (scoreEntryOrder A)

sparsemaxTemperature : Nat
sparsemaxTemperature = 16

record SparseWeight : Set where
  constructor sparseWeight
  field numerator denominator : Nat
open SparseWeight public

natAt : Nat → List Nat → Nat
natAt k [] = zero
natAt zero (x ∷ xs) = x
natAt (suc k) (x ∷ xs) = natAt k xs

sumList : List Nat → Nat
sumList [] = zero
sumList (x ∷ xs) = x + sumList xs

topCodes : ∀ {A} → Nat → List (ScoreEntry A) → List Nat
topCodes zero xs = []
topCodes (suc k) [] = []
topCodes (suc k) ((x , a) ∷ xs) = toℕ (code x) ∷ topCodes k xs

supportValid : ∀ {A} → List (ScoreEntry A) → Nat → Nat → BoolLike
supportValid xs temperature k with natLt (sumList (topCodes k xs)) ((k * natAt (k ∸ 1) (topCodes k xs)) + temperature)
... | yes = yes
... | no = no

searchSupport : ∀ {A} → List (ScoreEntry A) → Nat → Nat → Nat → Nat → Nat
searchSupport xs temperature zero current best = best
searchSupport xs temperature (suc n) current best with supportValid xs temperature current
... | yes = searchSupport xs temperature n (suc current) (maxNat best current)
... | no = searchSupport xs temperature n (suc current) best

supportSize : ∀ {A} → ActionSpace A → QVec A → CountVec A → Nat
supportSize {A} K q c = searchSupport (sortScores (scoreList q c)) sparsemaxTemperature A (suc zero) (suc zero)

sparsemaxWeight : ∀ {A} → ActionSpace A → QVec A → CountVec A → Fin A → SparseWeight
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

selectPositive : ∀ {A} → ActionSpace A → QVec A → CountVec A → List (ScoreEntry A) → Fin A
selectPositive K q c [] = witness K
selectPositive K q c ((s , a) ∷ xs) with weightPositive (sparsemaxWeight K q c a)
... | yes = a
... | no = selectPositive K q c xs

sparsemaxPolicy : ∀ {A} → ActionSpace A → QVec A → CountVec A → Fin A
sparsemaxPolicy K q c = selectPositive K q c (sortScores (scoreList q c))

actionSpace2 : ActionSpace 2
actionSpace2 = actionSpace (fromℕ< (m%n<n 0 2))

actionSpace4 : ActionSpace 4
actionSpace4 = actionSpace (fromℕ< (m%n<n 0 4))

defaultActionSpace : ActionSpace 64
defaultActionSpace = actionSpace (fromℕ< (m%n<n 0 64))

defaultD : Nat
defaultD = 64

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

identityMobius : MobiusAction
identityMobius = mobiusAction (λ x → x)

composeMobius : MobiusAction → MobiusAction → MobiusAction
composeMobius f g = mobiusAction (λ x → run f (run g x))

record MobiusTrace : Set where
  constructor mobiusTrace
  field atDepth : Nat → MobiusAction
open MobiusTrace public

prefixAction : MobiusTrace → Nat → MobiusAction
prefixAction T zero = identityMobius
prefixAction T (suc n) = composeMobius (atDepth T n) (prefixAction T n)

data HardSign : Set where
  negative zeroSign positive : HardSign

hardSign : Int8 → HardSign
hardSign x with natLt (toℕ (code x)) 128
... | yes with natEq (toℕ (code x)) zero
...   | yes = zeroSign
...   | no = positive
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

gruTransitionFamily : Set
gruTransitionFamily = Int8 → GRUState → GRUState

mobiusTransport : MobiusAction → gruTransitionFamily → gruTransitionFamily
mobiusTransport f T x s = T (run f x) s

record SemidirectToken : Set where
  constructor semidirectToken
  field transitionPart : gruTransitionFamily
        mobiusPart : MobiusAction
open SemidirectToken public

semidirectIdentity : SemidirectToken
semidirectIdentity = semidirectToken (λ x s → gruStep s x) identityMobius

semidirectCompose : SemidirectToken → SemidirectToken → SemidirectToken
semidirectCompose (semidirectToken T f) (semidirectToken S g) =
  semidirectToken
    (λ x s → T x (S (run f x) s))
    (composeMobius f g)

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
  field
    clock : Nat
    q : QVec A
    counts : CountVec A
    lastAction : Fin A
    gru : GRUState
    optimizer : F4State
    normState : NormPair
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
    (normStep (normState s) (q s a) shaped)

iterateLearner : ∀ {A} → LearnerKernel A → Nat → LearnerState A → Int8 → LearnerState A
iterateLearner K zero s r = s
iterateLearner K (suc n) s r = learnerStep K (iterateLearner K n s r) r

finiteFunctionKernel : ∀ {A B} → (Fin A → Fin B) → (Fin A → Fin B)
finiteFunctionKernel f = f
