{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith where

open import Relation.Binary.PropositionalEquality using (_≢_)

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Level using (0ℓ)
open import Data.Nat using (_∸_; _≤_; _/_; z≤n; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n; ≤-decTotalOrder)
open import Data.Nat.DivMod using (m%n<n)
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

int8Neg : Int8 → Int8
int8Neg x = int8OfNat (256 ∸ toℕ (code x))

int8Sub : Int8 → Int8 → Int8
int8Sub x y = int8Add x (int8Neg y)

int8Mul : Int8 → Int8 → Int8
int8Mul x y = int8OfNat (toℕ (code x) * toℕ (code y))

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

natLE : Nat → Nat → BoolLike
natLE zero n = yes
natLE (suc m) zero = no
natLE (suc m) (suc n) = natLE m n

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

maxNat-left-positive : ∀ {m n} → m ≢ zero → maxNat m n ≢ zero
maxNat-left-positive {zero} {n} h eq = h refl
maxNat-left-positive {suc m} {zero} h ()
maxNat-left-positive {suc m} {suc n} h ()

searchSupport-positive : ∀ {A} (xs : List (ScoreEntry A)) temperature fuel current best →
  best ≢ zero →
  searchSupport xs temperature fuel current best ≢ zero
searchSupport-positive xs temperature zero current best h = h
searchSupport-positive xs temperature (suc n) current best h with supportValid xs temperature current
... | yes =
  searchSupport-positive
    xs temperature n (suc current) (maxNat best current)
    (maxNat-left-positive h)
... | no =
  searchSupport-positive
    xs temperature n (suc current) best h


supportSize : ∀ {A} → ActionSpace A → QVec A → CountVec A → Nat
supportSize {A} K q c = searchSupport (sortScores (scoreList q c)) sparsemaxTemperature A (suc zero) (suc zero)

sparsemax-support-nonempty : ∀ {A} (K : ActionSpace A) (q : QVec A) (c : CountVec A) →
  supportSize K q c ≢ zero
sparsemax-support-nonempty K q c =
  searchSupport-positive
    (sortScores (scoreList q c))
    sparsemaxTemperature
    A
    (suc zero)
    (suc zero)
    (λ ())

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

data HardSign : Set where
  negative zeroSign positive : HardSign

hardSignNonnegative : Int8 → HardSign
hardSignNonnegative x with natEq (toℕ (code x)) zero
... | yes = zeroSign
... | no = positive

hardSign : Int8 → HardSign
hardSign x with natLt (toℕ (code x)) 128
... | yes = hardSignNonnegative x
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
  let z = hardSignGate x
      h = hiddenState s
      delta = int8Mul z (int8Sub x h)
      h′ = int8Add h delta
  in gruState
    h′
    (matrixZ s) (matrixR s) (matrixH s)
    (noiseZ s) (noiseR s) (noiseH s)
    (optimizerToken s) (l2Token s)

gruPersistent : GRUState → Int8 × (Int8 × (Int8 × Int8))
gruPersistent s = matrixZ s , (matrixR s , (matrixH s , optimizerToken s))

data F4Z : Set where
  f4Pos : Nat → F4Z
  f4NegZVal : Nat → F4Z

f4NegOfNat : Nat → F4Z
f4NegOfNat zero = f4Pos zero
f4NegOfNat (suc n) = f4NegZVal n

f4NegZ : F4Z → F4Z
f4NegZ (f4Pos zero) = f4Pos zero
f4NegZ (f4Pos (suc n)) = f4NegZVal n
f4NegZ (f4NegZVal n) = f4Pos (suc n)

f4AddZ : F4Z → F4Z → F4Z
f4AddZ (f4Pos m) (f4Pos n) = f4Pos (m + n)
f4AddZ (f4Pos m) (f4NegZVal n) with natLE m (suc n)
... | yes = f4NegZVal (n ∸ m)
... | no = f4Pos (m ∸ suc n)
f4AddZ (f4NegZVal m) (f4Pos n) = f4AddZ (f4Pos n) (f4NegZVal m)
f4AddZ (f4NegZVal m) (f4NegZVal n) = f4NegZVal (m + n + 1)

f4MulZ : F4Z → F4Z → F4Z
f4MulZ (f4Pos m) (f4Pos n) = f4Pos (m * n)
f4MulZ (f4Pos m) (f4NegZVal n) = f4NegZ (f4Pos (m * suc n))
f4MulZ (f4NegZVal m) (f4Pos n) = f4NegZ (f4Pos (suc m * n))
f4MulZ (f4NegZVal m) (f4NegZVal n) = f4Pos (suc m * suc n)

toF4Z : Int8 → F4Z
toF4Z x with natLE (toℕ (code x)) 127
... | yes = f4Pos (toℕ (code x))
... | no = f4NegZVal (255 ∸ toℕ (code x))

wrapF4Z : F4Z → Int8
wrapF4Z (f4Pos n) = int8OfNat n
wrapF4Z (f4NegZVal n) = int8Neg (int8OfNat (suc n))

f4Add : Int8 → Int8 → Int8
f4Add = int8Add

f4Neg8 : Int8 → Int8
f4Neg8 = int8Neg

f4Sub : Int8 → Int8 → Int8
f4Sub = int8Sub

f4Div128 : F4Z → F4Z
f4Div128 (f4Pos n) = f4Pos (n / 128)
f4Div128 (f4NegZVal n) = f4NegOfNat ((suc n + 127) / 128)

scaledF4 : Int8 → Int8 → Int8
scaledF4 x y = wrapF4Z (f4Div128 (f4MulZ (toF4Z x) (toF4Z y)))

f4Sign : Int8 → Int8
f4Sign x with toF4Z x
... | f4Pos zero = zero8
... | f4Pos (suc _) = one8
... | f4NegZVal _ = int8OfNat 255

f4SignZ : Int8 → F4Z
f4SignZ x with toF4Z x
... | f4Pos zero = f4Pos zero
... | f4Pos (suc _) = f4Pos 1
... | f4NegZVal _ = f4NegZVal zero

f4Pow2Nat : Nat → Nat
f4Pow2Nat zero = 1
f4Pow2Nat (suc n) = 2 * f4Pow2Nat n

f4Pow2Level : F4Z → Int8
f4Pow2Level (f4NegZVal _) = zero8
f4Pow2Level (f4Pos n) with natLE n 6
... | yes = int8OfNat (f4Pow2Nat n)
... | no = int8OfNat 127

record F4State : Set where
  constructor f4State
  field
    thetaQ residualQ errorQ errorResidual levelResidual : Int8
    level : F4Z
open F4State public

record F4Params : Set where
  constructor f4Params
  field beta₂ betaTheta : Int8
open F4Params public

zeroF4 : F4State
zeroF4 = f4State zero8 zero8 zero8 zero8 zero8 (f4Pos zero)

defaultF4Params : F4Params
defaultF4Params = f4Params zero8 zero8

f4ThetaFull : F4State → Int8
f4ThetaFull s = f4Add (thetaQ s) (residualQ s)

f4ErrorFull : F4State → Int8
f4ErrorFull s = f4Add (errorQ s) (errorResidual s)

f4ErrorNew : F4Params → F4State → Int8 → Int8
f4ErrorNew p s g =
  f4Add
    (scaledF4 (beta₂ p) (f4ErrorFull s))
    (scaledF4 (f4Sub one8 (beta₂ p)) g)

f4LevelUpdated : F4State → Int8 → F4Z
f4LevelUpdated s e′ =
  f4AddZ (level s) (f4SignZ (f4Add (levelResidual s) e′))

f4LevelResidualUpdated : F4State → Int8 → Int8
f4LevelResidualUpdated s e′ =
  let r′ = f4Add (levelResidual s) e′
  in f4Sub r′ (f4Sign r′)

f4DeltaTheta : F4Params → F4State → Int8 → Int8
f4DeltaTheta p s g =
  f4Sub
    (scaledF4 (f4Pow2Level (level s)) (hardSignGate g))
    (scaledF4 (betaTheta p) (f4ThetaFull s))

f4Step : F4Params → F4State → Int8 → F4State
f4Step p s g =
  f4State qθ′ rθ′ qe′ re′ rℓ′′ level′
  where
  θ = f4ThetaFull s
  e = f4ErrorFull s
  e′ = f4ErrorNew p s g
  rℓ′′ = f4LevelResidualUpdated s e′
  level′ = f4LevelUpdated s e′
  Δθ = f4DeltaTheta p s g
  qθ′ = f4Add θ Δθ
  rθ′ = f4Sub θ qθ′
  qe′ = e′
  re′ = f4Sub e e′

record NormPair : Set where
  constructor normPair
  field l1Weight pathWeight : Nat
open NormPair public

zeroNorm : NormPair
zeroNorm = normPair zero zero

int8AbsCode : Int8 → Nat
int8AbsCode x with natLE (toℕ (code x)) 127
... | yes = toℕ (code x)
... | no = 256 ∸ toℕ (code x)

normStep : NormPair → Int8 → Int8 → NormPair
normStep n w x =
  normPair
    (l1Weight n + int8AbsCode w)
    (pathWeight n + (int8AbsCode w * int8AbsCode x))

data MunchausenMode : Set where
  munchausen noMunchausen : MunchausenMode

munchausenScale8 : Nat
munchausenScale8 = 16

finiteQLog2Bias : SparseWeight → Int8
finiteQLog2Bias (sparseWeight n d) with natEq n zero
... | yes = zero8
... | no with natLE n d
... | yes = int8Neg (int8OfNat ((munchausenScale8 * (d ∸ n)) / n))
... | no = int8OfNat ((munchausenScale8 * (n ∸ d)) / n)

negativeMunchausen : SparseWeight → Int8
negativeMunchausen = finiteQLog2Bias

munchausenSignal : MunchausenMode → SparseWeight → Int8
munchausenSignal munchausen w = finiteQLog2Bias w
munchausenSignal noMunchausen w = zero8

record LearnerKernel (A : Nat) : Set where
  constructor learnerKernel
  field
    actionSpaceK : ActionSpace A
    mode : MunchausenMode
    f4ParamsK : F4Params
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
    (f4Step (f4ParamsK K) (optimizer s) shaped)
    (normStep (normState s) (q s a) shaped)

iterateLearner : ∀ {A} → LearnerKernel A → Nat → LearnerState A → Int8 → LearnerState A
iterateLearner K zero s reward = s
iterateLearner K (suc n) s reward = learnerStep K (iterateLearner K n s reward) reward
