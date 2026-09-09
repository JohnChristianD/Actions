{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_CReLU_Tsallis2_v150 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _* )
open import Agda.Builtin.Equality using (_≡_; refl)

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data Bool : Set where
  false true : Bool

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

sumV : ∀ {A : Set} → (A → A → A) → A → ∀ {n} → Vec A n → A
sumV _ z [] = z
sumV op z (x ∷ xs) = op x (sumV op z xs)

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

record Algebra : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg abs : R → R
    _≤_ : R → R → Set
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

open Algebra

Vector : Algebra → Nat → Set
Vector A n = Vec (Algebra.R A) n

Matrix : Algebra → Nat → Nat → Set
Matrix A m n = Vec (Vec (Algebra.R A) n) m

rowL1 : ∀ {A n} → Algebra A → Vec (Algebra.R A) n → Algebra.R A
rowL1 A [] = zero A
rowL1 A (x ∷ xs) = abs A x +A rowL1 A xs
  where
  infixl 6 _+A_
  _+A_ : Algebra.R A → Algebra.R A → Algebra.R A
  _+A_ = Algebra._+_ A

weightL1 : ∀ {A m n} → Algebra A → Matrix A m n → Algebra.R A
weightL1 A [] = zero A
weightL1 A (r ∷ rs) = Algebra._+_ A (rowL1 A r) (weightL1 A rs)

pathRow : ∀ {A h i} → Algebra A → Vec (Algebra.R A) h → Matrix A h i → Algebra.R A
pathRow A [] [] = zero A
pathRow A (a ∷ as) (r ∷ rs) =
  Algebra._+_ A
    (Algebra._*_ A (abs A a) (rowL1 A r))
    (pathRow A as rs)

onePathNorm : ∀ {A h i o} → Algebra A → Matrix A h i → Matrix A o h → Algebra.R A
onePathNorm A W1 [] = zero A
onePathNorm A W1 (r ∷ rs) =
  Algebra._+_ A (pathRow A r W1) (onePathNorm A W1 rs)

record NormCertificate (A : Algebra) : Set₁ where
  field
    l1Bound path1Bound sensitivityBound : Algebra.R A
    l1Witness path1Witness : Algebra.R A
    l1LeBound : Algebra._≤_ A l1Witness l1Bound
    path1LeBound : Algebra._≤_ A path1Witness path1Bound

cplus : ∀ {A} → Algebra A → Algebra.R A → Algebra.R A
cplus A x = max A (zero A) x

cminus : ∀ {A} → Algebra A → Algebra.R A → Algebra.R A
cminus A x = max A (zero A) (neg A x)

record CReLULaws (A : Algebra) : Set₁ where
  field
    reconstruct : ∀ x →
      Algebra._+_ A (cplus A x) (neg A (cminus A x)) ≡ x
    absDecompose : ∀ x →
      Algebra._+_ A (cplus A x) (cminus A x) ≡ abs A x
    positiveChannelBound : ∀ x → zero A ≤A cplus A x
    negativeChannelBound : ∀ x → zero A ≤A cminus A x
  where
  infix 4 _≤A_
  _≤A_ = Algebra._≤_ A

index : ∀ {A n X} → Fin n → Vec X n → X
index fzero (x ∷ _) = x
index (fsuc i) (_ ∷ xs) = index i xs
  where
  data Fin : Nat → Set where
    fzero : {n : Nat} → Fin (suc n)
    fsuc : {n : Nat} → Fin n → Fin (suc n)

record Tsallis2Branch (A : Algebra) (n : Nat) : Set₁ where
  field
    scores tau weights : Vector A n
    active : Vec Bool n
    nonnegative : ∀ i → Algebra._≤_ A (zero A) (index i weights)
    inactiveZero : ∀ i → index i active ≡ false → index i weights ≡ zero A
    activeAffine : ∀ i → index i active ≡ true →
      index i weights ≡ Algebra._+_ A (index i scores) (neg A tau)
    normalized : sumV (Algebra._+_ A) (zero A) weights ≡ one A

zeros : ∀ {A n} → Algebra A → Vector A n
zeros A {zero} = []
zeros A {suc n} = zero A ∷ zeros A

record QProjection (A : Algebra) (n : Nat) : Set₁ where
  field
    project : Vector A n → Vector A n
    idempotent : ∀ x → project (project x) ≡ project x
    preservesZero : project (zeros A) ≡ zeros A

record DyadicScales (A : Algebra) : Set₁ where
  field
    scale : Nat → Algebra.R A
    scaleZero : scale zero ≡ one A
    halfLaw : ∀ k → Algebra._+_ A (scale (suc k)) (scale (suc k)) ≡ scale k

record CompositeBranch (A : Algebra) (n : Nat) : Set₁ where
  field
    forwardTag attentionTag updateTag : Vec Bool n

record CompositeCertificate (A : Algebra) (n : Nat) : Set₁ where
  field
    crelu : CReLULaws A
    attention : Tsallis2Branch A n
    projection : QProjection A n
    dyadic : DyadicScales A
    norms : NormCertificate A
    branch : CompositeBranch A n

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc k) = 3 * pow3 k

attentionDegreeStep : Nat → Nat
attentionDegreeStep d = 3 * d

finiteDegreeLaw : ∀ k → attentionDegreeStep (pow3 k) ≡ pow3 (suc k)
finiteDegreeLaw zero = refl
finiteDegreeLaw (suc k) = refl

record EfficientCHAD_CReLU_Tsallis2_TheoremTarget (A : Algebra) (n : Nat) : Set₁ where
  field
    certificate : CompositeCertificate A n
    sparseEquilibrium : ∀ i →
      Tsallis2Branch.active (CompositeCertificate.attention certificate) i ≡ true →
      Tsallis2Branch.weights (CompositeCertificate.attention certificate) i ≡
        Algebra._+_ A
          (Tsallis2Branch.scores (CompositeCertificate.attention certificate) i)
          (neg A (Tsallis2Branch.tau (CompositeCertificate.attention certificate)))
    creluReconstruction : ∀ x →
      Algebra._+_ A (cplus A x) (neg A (cminus A x)) ≡ x
    creluAbsDecomposition : ∀ x →
      Algebra._+_ A (cplus A x) (cminus A x) ≡ abs A x
    qProjectionIdempotent : ∀ x →
      QProjection.project (CompositeCertificate.projection certificate)
        (QProjection.project (CompositeCertificate.projection certificate) x) ≡
      QProjection.project (CompositeCertificate.projection certificate) x
    degreeBound : ∀ k → attentionDegreeStep (pow3 k) ≡ pow3 (suc k)
    finiteOrderedClosure : CompositeCertificate A n → CompositeCertificate A n

assembleTheoremTarget : ∀ {A n} →
  CompositeCertificate A n →
  EfficientCHAD_CReLU_Tsallis2_TheoremTarget A n
assembleTheoremTarget c = record
  { certificate = c
  ; sparseEquilibrium = Tsallis2Branch.activeAffine (CompositeCertificate.attention c)
  ; creluReconstruction = CReLULaws.reconstruct (CompositeCertificate.crelu c)
  ; creluAbsDecomposition = CReLULaws.absDecompose (CompositeCertificate.crelu c)
  ; qProjectionIdempotent = QProjection.idempotent (CompositeCertificate.projection c)
  ; degreeBound = finiteDegreeLaw
  ; finiteOrderedClosure = λ x → x
  }
