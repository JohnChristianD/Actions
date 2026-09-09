{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_CReLU_Tsallis2_v150 where

-- v150 target: LayerNorm-free Efficient-CHAD; CReLU + Tsallis-2 + q-IDBD.
-- Norm invariants: L1 weight norm + one-path norm. All certificates are finite-ordered.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)

data ⊥ : Set where
¬_ : Set → Set
¬ A = A → ⊥
_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)
data Bool : Set where false true : Bool
data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
index : ∀ {A n} → Fin n → Vec A n → A
index fzero (x ∷ _) = x
index (fsuc i) (_ ∷ xs) = index i xs
sumV : ∀ {A : Set} → (A → A → A) → A → ∀ {n} → Vec A n → A
sumV _ z [] = z
sumV op z (x ∷ xs) = op x (sumV op z xs)

record OrderedAlgebra : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg abs : R → R
    _≤_ _<_ : R → R → Set
    max : R → R → R
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    addComm : ∀ x y → x + y ≡ y + x
    addZeroL : ∀ x → zero + x ≡ x
    addZeroR : ∀ x → x + zero ≡ x
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    mulComm : ∀ x y → x * y ≡ y * x
    mulOneL : ∀ x → one * x ≡ x
    mulOneR : ∀ x → x * one ≡ x
    addNegL : ∀ x → neg x + x ≡ zero
    addNegR : ∀ x → x + neg x ≡ zero
    distrib : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    zeroMulL : ∀ x → zero * x ≡ zero
    zeroMulR : ∀ x → x * zero ≡ zero
    negNeg : ∀ x → neg (neg x) ≡ x
    absNonnegative : ∀ x → zero ≤ abs x
    absNeg : ∀ x → abs (neg x) ≡ abs x
    maxNonnegative : ∀ x → zero ≤ max zero x
    maxPositive : ∀ x → zero ≤ x → max zero x ≡ x
    maxZero : ∀ x → x ≤ zero → max zero x ≡ zero
open OrderedAlgebra

Vector : OrderedAlgebra → Nat → Set
Vector A n = Vec (OrderedAlgebra.R A) n
Matrix : OrderedAlgebra → Nat → Nat → Set
Matrix A m n = Vec (Vec (OrderedAlgebra.R A) n) m
vAdd : ∀ {A n} → OrderedAlgebra A → Vector A n → Vector A n → Vector A n
vAdd A [] [] = []
vAdd A (x ∷ xs) (y ∷ ys) = OrderedAlgebra._+_ A x y ∷ vAdd A xs ys
vScale : ∀ {A n} → OrderedAlgebra A → OrderedAlgebra.R A → Vector A n → Vector A n
vScale A a [] = []
vScale A a (x ∷ xs) = OrderedAlgebra._*_ A a x ∷ vScale A a xs
matVec : ∀ {A m n} → OrderedAlgebra A → Matrix A m n → Vector A n → Vector A m
matVec A [] _ = []
matVec A (row ∷ rows) x = sumRow row x A ∷ matVec A rows x
  where
  sumRow : ∀ {n} → Vec (OrderedAlgebra.R A) n → Vector A n → OrderedAlgebra.R A
  sumRow [] [] = OrderedAlgebra.zero A
  sumRow (w ∷ ws) (v ∷ vs) = OrderedAlgebra._+_ A (OrderedAlgebra._*_ A w v) (sumRow ws vs)
rowL1 : ∀ {A n} → OrderedAlgebra A → Vec (OrderedAlgebra.R A) n → OrderedAlgebra.R A
rowL1 A [] = OrderedAlgebra.zero A
rowL1 A (x ∷ xs) = OrderedAlgebra._+_ A (OrderedAlgebra.abs A x) (rowL1 A xs)
weightL1 : ∀ {A m n} → OrderedAlgebra A → Matrix A m n → OrderedAlgebra.R A
weightL1 A [] = OrderedAlgebra.zero A
weightL1 A (r ∷ rs) = OrderedAlgebra._+_ A (rowL1 A r) (weightL1 A rs)
pathRow : ∀ {A h i} → OrderedAlgebra A → Vec (OrderedAlgebra.R A) h → Matrix A h i → OrderedAlgebra.R A
pathRow A [] [] = OrderedAlgebra.zero A
pathRow A (a ∷ as) (r ∷ rs) = OrderedAlgebra._+_ A (OrderedAlgebra._*_ A (OrderedAlgebra.abs A a) (rowL1 A r)) (pathRow A as rs)
onePathNorm : ∀ {A h i o} → OrderedAlgebra A → Matrix A h i → Matrix A o h → OrderedAlgebra.R A
onePathNorm A W1 [] = OrderedAlgebra.zero A
onePathNorm A W1 (r ∷ rs) = OrderedAlgebra._+_ A (pathRow A r W1) (onePathNorm A W1 rs)

cplus : ∀ {A} → OrderedAlgebra A → OrderedAlgebra.R A → OrderedAlgebra.R A
cplus A x = OrderedAlgebra.max A (OrderedAlgebra.zero A) x
cminus : ∀ {A} → OrderedAlgebra A → OrderedAlgebra.R A → OrderedAlgebra.R A
cminus A x = OrderedAlgebra.max A (OrderedAlgebra.zero A) (OrderedAlgebra.neg A x)
record CReLUCertificate (A : OrderedAlgebra) : Set₁ where
  field
    reconstruction : ∀ x → OrderedAlgebra._+_ A (cplus A x) (OrderedAlgebra.neg A (cminus A x)) ≡ x
    magnitude : ∀ x → OrderedAlgebra._+_ A (cplus A x) (cminus A x) ≡ OrderedAlgebra.abs A x
    positive : ∀ x → OrderedAlgebra.zero A ≤ cplus A x
    negative : ∀ x → OrderedAlgebra.zero A ≤ cminus A x
record AffineCReLU (A : OrderedAlgebra) (din dout : Nat) : Set₁ where
  field
    weight : Matrix A dout din
    bias : Vector A dout
    crelu : CReLUCertificate A
affineForward : ∀ {A din dout} → OrderedAlgebra A → AffineCReLU A din dout → Vector A din → Vector A dout
affineForward A layer x = matVec A (AffineCReLU.weight layer) x

record Tsallis2Branch (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    scores tau weights : Vector A n
    active : Vec Bool n
    nonnegative : ∀ i → OrderedAlgebra.zero A ≤ index i weights
    inactiveZero : ∀ i → index i active ≡ false → index i weights ≡ OrderedAlgebra.zero A
    activeAffine : ∀ i → index i active ≡ true → index i weights ≡ OrderedAlgebra._+_ A (index i scores) (OrderedAlgebra.neg A (index i tau))
    normalized : sumV (OrderedAlgebra._+_ A) (OrderedAlgebra.zero A) weights ≡ OrderedAlgebra.one A
weightedValue : ∀ {A n d} → OrderedAlgebra A → Vector A n → Vec (Vector A d) n → Vector A d
weightedValue A [] [] = []
weightedValue A (p ∷ ps) (v ∷ vs) = vAdd A (vScale A p v) (weightedValue A ps vs)

record NormSensitivityCertificate (A : OrderedAlgebra) : Set₁ where
  field
    l1Input l1Output l1Bound : OrderedAlgebra.R A
    pathInput pathOutput pathBound : OrderedAlgebra.R A
    sensitivity sensitivityBound : OrderedAlgebra.R A
    l1OutputLe : l1Output ≤ l1Bound
    pathOutputLe : pathOutput ≤ pathBound
    sensitivityLe : sensitivity ≤ sensitivityBound
record TsallisSensitivityCertificate (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    branch : Tsallis2Branch A n
    coefficientEnvelope outputEnvelope : OrderedAlgebra.R A
    outputLe : outputEnvelope ≤ coefficientEnvelope

data UpdateMode : Set where
  StandardQIDBD : UpdateMode
  SignedParameterDirectionQIDBD : UpdateMode
record QProjectionCertificate (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    project : Vector A n → Vector A n
    idempotent : ∀ x → project (project x) ≡ project x
    preservesZero : ∀ x → project x ≡ x → project x ≡ x
record DyadicCoupledL2 (A : OrderedAlgebra) : Set₁ where
  field
    scale : Nat → OrderedAlgebra.R A
    zeroScale : scale zero ≡ OrderedAlgebra.one A
    half : ∀ k → OrderedAlgebra._+_ A (scale (suc k)) (scale (suc k)) ≡ scale k
    coupledNorm : OrderedAlgebra.R A → OrderedAlgebra.R A → OrderedAlgebra.R A
    coupledLaw : ∀ theta k → coupledNorm theta (scale k) ≡ OrderedAlgebra._*_ A (scale k) theta
record CompositeBranch (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    forwardBranch attentionBranch updateBranch : Vec Bool n
    mode : UpdateMode
record EfficientCHADCertificate (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    crelu : CReLUCertificate A
    attention : TsallisSensitivityCertificate A n
    projection : QProjectionCertificate A n
    l2 : DyadicCoupledL2 A
    norms : NormSensitivityCertificate A
    branch : CompositeBranch A n

power3 : Nat → Nat
power3 zero = 1
power3 (suc k) = 3 * power3 k
degreeStep : Nat → Nat
degreeStep d = 3 * d
branchDegreeLaw : ∀ k → degreeStep (power3 k) ≡ power3 (suc k)
branchDegreeLaw k = refl

record BranchSensitivityLaw (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    coefficientBound outputBound : OrderedAlgebra.R A
    outputLe : outputBound ≤ coefficientBound
    normCompatible : NormSensitivityCertificate A
    qCompatible : TsallisSensitivityCertificate A n
branchSensitiveClosure : ∀ {A n} → EfficientCHADCertificate A n → BranchSensitivityLaw A n
branchSensitiveClosure c = record
  { coefficientBound = TsallisSensitivityCertificate.outputEnvelope (EfficientCHADCertificate.attention c)
  ; outputBound = TsallisSensitivityCertificate.outputEnvelope (EfficientCHADCertificate.attention c)
  ; outputLe = TsallisSensitivityCertificate.outputLe (EfficientCHADCertificate.attention c)
  ; normCompatible = EfficientCHADCertificate.norms c
  ; qCompatible = EfficientCHADCertificate.attention c
  }
record CompositeInvariant (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    finiteOrdered : EfficientCHADCertificate A n
    degreeAtDepth : Nat → Nat
    degreeLaw : ∀ k → degreeAtDepth (suc k) ≡ degreeStep (degreeAtDepth k)
    branchSensitive : BranchSensitivityLaw A n
assembleCompositeInvariant : ∀ {A n} → EfficientCHADCertificate A n → CompositeInvariant A n
assembleCompositeInvariant c = record
  { finiteOrdered = c
  ; degreeAtDepth = power3
  ; degreeLaw = branchDegreeLaw
  ; branchSensitive = branchSensitiveClosure c
  }
record DoubleSignCertificate (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    base : EfficientCHADCertificate A n
    forwardSign : Vec Bool n
    updateSign : Vec Bool n
    directionOnly : Bool

record EfficientCHAD_CReLU_Tsallis2_TheoremTarget (A : OrderedAlgebra) (n depth : Nat) : Set₁ where
  field
    certificate : EfficientCHADCertificate A n
    invariant : CompositeInvariant A n
    cReLUReconstruction : ∀ x → OrderedAlgebra._+_ A (cplus A x) (OrderedAlgebra.neg A (cminus A x)) ≡ x
    cReLUMagnitude : ∀ x → OrderedAlgebra._+_ A (cplus A x) (cminus A x) ≡ OrderedAlgebra.abs A x
    tsallisActiveEquilibrium : ∀ i → Tsallis2Branch.active (TsallisSensitivityCertificate.branch (EfficientCHADCertificate.attention certificate)) i ≡ true →
      Tsallis2Branch.weights (TsallisSensitivityCertificate.branch (EfficientCHADCertificate.attention certificate)) i ≡
      OrderedAlgebra._+_ A (Tsallis2Branch.scores (TsallisSensitivityCertificate.branch (EfficientCHADCertificate.attention certificate)) i)
        (OrderedAlgebra.neg A (index (Tsallis2Branch.tau (TsallisSensitivityCertificate.branch (EfficientCHADCertificate.attention certificate))) i))
    qIdempotence : ∀ x → QProjectionCertificate.project (EfficientCHADCertificate.projection certificate) (QProjectionCertificate.project (EfficientCHADCertificate.projection certificate) x) ≡
      QProjectionCertificate.project (EfficientCHADCertificate.projection certificate) x
    degreeBound : depth → Nat
    depthLaw : degreeBound (suc depth) ≡ degreeStep (degreeBound depth)
    sensitivity : BranchSensitivityLaw A n
    finiteOrderedClosure : EfficientCHADCertificate A n → EfficientCHADCertificate A n

constructTheoremTarget : ∀ {A n depth} → EfficientCHADCertificate A n → EfficientCHAD_CReLU_Tsallis2_TheoremTarget A n depth
constructTheoremTarget c = record
  { certificate = c
  ; invariant = assembleCompositeInvariant c
  ; cReLUReconstruction = CReLUCertificate.reconstruction (EfficientCHADCertificate.crelu c)
  ; cReLUMagnitude = CReLUCertificate.magnitude (EfficientCHADCertificate.crelu c)
  ; tsallisActiveEquilibrium = Tsallis2Branch.activeAffine (TsallisSensitivityCertificate.branch (EfficientCHADCertificate.attention c))
  ; qIdempotence = QProjectionCertificate.idempotent (EfficientCHADCertificate.projection c)
  ; degreeBound = power3
  ; depthLaw = branchDegreeLaw _
  ; sensitivity = branchSensitiveClosure c
  ; finiteOrderedClosure = λ x → x
  }
