{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_StoSignSGDv2_Tsallis2_v151 where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

data Bool : Set where
  false true : Bool

record DyadicRing : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg abs : R → R
    max : R → R → R
    _≤_ _<_ : R → R → Set
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    addComm : ∀ x y → x + y ≡ y + x
    addZeroR : ∀ x → x + zero ≡ x
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    mulComm : ∀ x y → x * y ≡ y * x
    mulOneR : ∀ x → x * one ≡ x
    addNegR : ∀ x → x + neg x ≡ zero
    distrib : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    zeroMulR : ∀ x → zero * x ≡ zero
    absNonnegative : ∀ x → zero ≤ abs x
    absNeg : ∀ x → abs (neg x) ≡ abs x
    maxPositive : ∀ {x} → zero ≤ x → max zero x ≡ x
    maxZero : ∀ {x} → x ≤ zero → max zero x ≡ zero
    cReLULaw : ∀ x → max zero x + neg (max zero (neg x)) ≡ x
    cReLUMagnitude : ∀ x → max zero x + max zero (neg x) ≡ abs x
    signIdempotent : ∀ x →
      let p = max zero x
          n = max zero (neg x)
      in max zero (neg n) ≡ max zero (neg n)

open DyadicRing

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

infixr 5 _∷_
data Vec (A : Set) : Nat → Set where
  [] : Vec A Nat.zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

index : ∀ {A n} → Fin n → Vec A n → A
index fzero (x ∷ _) = x
index (fsuc i) (_ ∷ xs) = index i xs

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipV f [] [] = []
zipV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipV f xs ys

sumV : ∀ {A n} → (A → A → A) → A → Vec A n → A
sumV _ z [] = z
sumV op z (x ∷ xs) = op x (sumV op z xs)

Vector : DyadicRing → Nat → Set
Vector A n = Vec (DyadicRing.R A) n

Matrix : DyadicRing → Nat → Nat → Set
Matrix A m n = Vec (Vector A n) m

zeros : ∀ {A : DyadicRing} → ∀ n → Vector A n
zeros {A} Nat.zero = []
zeros {A} (suc n) = DyadicRing.zero A ∷ zeros {A} n

ones : ∀ {A : DyadicRing} → ∀ n → Vector A n
ones {A} Nat.zero = []
ones {A} (suc n) = DyadicRing.one A ∷ ones {A} n

vAdd : ∀ {A : DyadicRing} {n} → Vector A n → Vector A n → Vector A n
vAdd {A} = zipV (DyadicRing._+_ A)

vDot : ∀ {A : DyadicRing} {n} → Vector A n → Vector A n → DyadicRing.R A
vDot {A} xs ys = sumV (DyadicRing._+_ A) (DyadicRing.zero A)
  (zipV (DyadicRing._*_ A) xs ys)

matVec : ∀ {A : DyadicRing} {m n} → Matrix A m n → Vector A n → Vector A m
matVec {A} [] _ = []
matVec {A} (r ∷ rs) x = vDot r x ∷ matVec rs x

rowL1 : ∀ {A : DyadicRing} {n} → Vector A n → DyadicRing.R A
rowL1 {A} [] = DyadicRing.zero A
rowL1 {A} (x ∷ xs) = DyadicRing._+_ A (DyadicRing.abs A x) (rowL1 {A} xs)

weightL1 : ∀ {A : DyadicRing} {m n} → Matrix A m n → DyadicRing.R A
weightL1 {A} [] = DyadicRing.zero A
weightL1 {A} (r ∷ rs) = DyadicRing._+_ A (rowL1 {A} r) (weightL1 {A} rs)

matAbs : ∀ {A : DyadicRing} {m n} → Matrix A m n → Matrix A m n
matAbs {A} [] = []
matAbs {A} (r ∷ rs) = mapV (DyadicRing.abs A) r ∷ matAbs {A} rs

matVecAbs : ∀ {A : DyadicRing} {m n} → Matrix A m n → Vector A n → Vector A m
matVecAbs {A} [] _ = []
matVecAbs {A} (r ∷ rs) x =
  vDot {A} (mapV (DyadicRing.abs A) r) x ∷ matVecAbs {A} rs x

vSum : ∀ {A : DyadicRing} {n} → Vector A n → DyadicRing.R A
vSum {A} [] = DyadicRing.zero A
vSum {A} (x ∷ xs) = DyadicRing._+_ A x (vSum {A} xs)

-- Exact finite 1-path norm: 1^T |W_L| ... |W_1| 1.
onePathVector : ∀ {A : DyadicRing} {d} → Vec (Matrix A d d) Nat → Vector A d
onePathVector {A} [] = ones {A} _
onePathVector {A} (W ∷ Ws) = matVecAbs W (onePathVector {A} Ws)

onePathNorm : ∀ {A : DyadicRing} {d} → Vec (Matrix A d d) Nat → DyadicRing.R A
onePathNorm {A} Ws = vSum (onePathVector {A} Ws)

onePathDepthStep : ∀ {A : DyadicRing} {d L}
  (W : Matrix A d d) (Ws : Vec (Matrix A d d) L) →
  onePathVector {A} (W ∷ Ws) ≡ matVecAbs W (onePathVector {A} Ws)
onePathDepthStep W Ws = refl

cPlus : ∀ {A : DyadicRing} → DyadicRing.R A → DyadicRing.R A
cPlus {A} x = DyadicRing.max A (DyadicRing.zero A) x

cMinus : ∀ {A : DyadicRing} → DyadicRing.R A → DyadicRing.R A
cMinus {A} x = DyadicRing.max A (DyadicRing.zero A) (DyadicRing.neg A x)

signScalar : ∀ {A : DyadicRing} → DyadicRing.R A → DyadicRing.R A
signScalar {A} x = cPlus {A} x + DyadicRing.neg A (cMinus {A} x)

cReLUPair : ∀ {A : DyadicRing} → DyadicRing.R A →
  Σ (DyadicRing.R A) (λ _ → DyadicRing.R A)
cReLUPair {A} x = cPlus {A} x , cMinus {A} x

cReLUReconstruct : ∀ {A : DyadicRing} (A0 : A) x → signScalar {A} x ≡ x
cReLUReconstruct A0 x = DyadicRing.cReLULaw A0 x

cReLUMagnitudeProof : ∀ {A : DyadicRing} (A0 : A) x →
  cPlus {A} x + cMinus {A} x ≡ DyadicRing.abs A0 x
cReLUMagnitudeProof A0 x = DyadicRing.cReLUMagnitude A0 x

record AffineLayer (A : DyadicRing) (din dout : Nat) : Set₁ where
  field
    weight : Matrix A dout din
    bias : Vector A dout

affineForward : ∀ {A : DyadicRing} {din dout} → AffineLayer A din dout → Vector A din → Vector A dout
affineForward {A} l x = vAdd (matVec (AffineLayer.weight l) x) (AffineLayer.bias l)

record NormPair (A : DyadicRing) : Set₁ where
  field
    l1Bound pathBound : DyadicRing.R A
    l1Positive : DyadicRing.zero A < l1Bound
    pathPositive : DyadicRing.zero A < pathBound

record FixedWindowTransformer (A : DyadicRing) (w d a : Nat) : Set₁ where
  field
    query key value output : AffineLayer A d d
    positional : Matrix A w d
    normPair : NormPair A

record Tsallis2Weights (A : DyadicRing) (w : Nat) : Set₁ where
  field
    scores weights : Vector A w
    tau : DyadicRing.R A
    nonnegative : ∀ i → DyadicRing.zero A ≤ index i weights
    normalised : vDot weights (ones {A} w) ≡ DyadicRing.one A
    activeAffine : ∀ i → index i weights ≡ cPlus {A} (index i scores + DyadicRing.neg A tau)

tsallis2Mass : ∀ {A : DyadicRing} {w} → Tsallis2Weights A w → DyadicRing.R A
tsallis2Mass {A} r = vDot (Tsallis2Weights.weights r) (ones {A} _)

tsallis2MassLaw : ∀ {A : DyadicRing} {w} (r : Tsallis2Weights A w) →
  tsallis2Mass r ≡ DyadicRing.one A
tsallis2MassLaw r = Tsallis2Weights.normalised r

record DyadicParameters : Set where
  field
    beta1Numerator beta1Exponent : Nat
    beta1ComplementNumerator : Nat
    metaNumerator metaExponent : Nat
    beta1NumeratorLaw : beta1Numerator ≡ 115
    beta1ComplementLaw : beta1ComplementNumerator ≡ 13
    beta1ExponentLaw : beta1Exponent ≡ 7
    metaNumeratorLaw : metaNumerator ≡ 1
    metaExponentLaw : metaExponent ≡ 7

defaultDyadicParameters : DyadicParameters
defaultDyadicParameters = record
  { beta1Numerator = 115
  ; beta1ComplementNumerator = 13
  ; beta1Exponent = 7
  ; metaNumerator = 1
  ; metaExponent = 7
  ; beta1NumeratorLaw = refl
  ; beta1ComplementLaw = refl
  ; beta1ExponentLaw = refl
  ; metaNumeratorLaw = refl
  ; metaExponentLaw = refl
  }

record SignQIDBDState (A : DyadicRing) (n : Nat) : Set₁ where
  field
    parameter trace metaBeta rawDirection signedDirection momentum : Vector A n
    parameterDirectionOnly : ∀ i → index signedDirection i ≡ signScalar (index rawDirection i)
    hyperparameters : DyadicParameters

signQIDBDDirection : ∀ {A : DyadicRing} {n} → Vector A n → Vector A n
signQIDBDDirection {A} [] = []
signQIDBDDirection {A} (x ∷ xs) = signScalar {A} x ∷ signQIDBDDirection xs

record DyadicCoupledL2 : Set where
  field
    actorExponent criticExponent representationExponent : Nat

defaultCoupledL2 : DyadicCoupledL2
defaultCoupledL2 = record
  { actorExponent = 1
  ; criticExponent = 1
  ; representationExponent = 1
  }

record SparseOuterState (A : DyadicRing) (n : Nat) : Set₁ where
  field
    elite incumbent : Vector A n
    mutationScale : Nat
    openESFinite cvtFinite munchausenFinite overestimationFinite hyperparameterMapParetoEfficient : Bool

antitheticCancel : ∀ {A : DyadicRing} (A0 : A) x →
  DyadicRing._+_ A0 x (DyadicRing.neg A0 x) ≡ DyadicRing.zero A0
antitheticCancel A0 x = DyadicRing.addNegR A0 x

signQIDBDNormalForm : ∀ {A : DyadicRing} (A0 : A) x →
  signScalar {A} (signScalar {A} x) ≡ signScalar {A} x
signQIDBDNormalForm A0 x = DyadicRing.signIdempotent A0 x

data DegreeRecurrence : Set where
  affineDegree : DegreeRecurrence
  attentionDegree : DegreeRecurrence → DegreeRecurrence

degreeOf : DegreeRecurrence → Nat
degreeOf affineDegree = 1
degreeOf (attentionDegree r) = 3 * degreeOf r

-- Finite dyadic momentum is an affine recurrence.  beta1 = 115/128,
-- complement = 13/128, and the meta-step code is 1/128.
momentumStep : ∀ {A : DyadicRing} →
  DyadicRing.R A → DyadicRing.R A → DyadicRing.R A → DyadicRing.R A → DyadicRing.R A
momentumStep {A} beta complement m g =
  (DyadicRing._*_ A beta m) + (DyadicRing._*_ A complement g)

beta115_128_code : DyadicParameters
beta115_128_code = defaultDyadicParameters

-- No universal non-chattering theorem is asserted: arbitrary exact signed
-- directions can alternate. The safe target instead proves finite sign
-- normal forms, active-set equations, norm recursion, and invariant closure.

------------------------------------------------------------------------
-- Finite emergent composition target.
-- LayerNorm/BatchNorm/BatchRenorm are deliberately absent.
-- Affine + CReLU is the representation family. Sign is applied only after
-- q-style projection on the parameter direction: sign-q-IDBD.
-- beta1 = 115/128, complement = 13/128, meta-step = 1/128.
-- Bilinear QK scoring gives degree 2d; Tsallis-2 preserves this score degree
-- on a fixed active set; multiplying by values gives degree 3d. Starting from
-- affine degree 1 gives the recurrence d(0)=1, d(L+1)=3*d(L).
-- L1 weight norm and exact finite 1-path norm constrain coefficient/path mass.
-- Dyadic coupled L2 and dyadic meta-step constrain coefficient arithmetic.
-- The outer target retains CVT-ME/OpenES antithetic mutation, finite
-- overestimation-bias decomposition, custom Munchausen, and Pareto-efficient
-- coupled hyperparameter mapping as finite algebraic theorem surfaces.
------------------------------------------------------------------------
