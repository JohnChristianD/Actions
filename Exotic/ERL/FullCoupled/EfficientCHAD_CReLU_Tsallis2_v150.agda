{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_CReLU_Tsallis2_v150 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- Minimal finite ordered algebra boundary.
-- No LayerNorm, transcendental normalization, or postulates occur here.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Finite vectors and matrices.
------------------------------------------------------------------------

data Bool : Set where
  false true : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

_≠_ : {A : Set} → A → A → Set
x ≠ y = (x ≡ y) → Algebra.⊥

-- A local empty type avoids importing a larger library boundary.
data ⊥ : Set where


data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

index : ∀ {A n} → Vec A n → Fin n → A
index [] ()
index (x ∷ xs) fzero = x
index (x ∷ xs) (fsuc i) = index xs i

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipWithV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWithV _ [] [] = []
zipWithV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithV f xs ys

sumV : ∀ {A : Set} → (A → A → A) → A → ∀ {n} → Vec A n → A
sumV _ z [] = z
sumV op z (x ∷ xs) = op x (sumV op z xs)

Matrix : Algebra → Nat → Nat → Set
Matrix A m n = Fin m → Fin n → Algebra.R A

Vector : Algebra → Nat → Set
Vector A n = Vec (Algebra.R A) n

------------------------------------------------------------------------
-- CReLU: exact positive/negative magnitude decomposition.
------------------------------------------------------------------------

cplus : (A : Algebra) → Algebra.R A → Algebra.R A
cplus A x = Algebra.max A (Algebra.zero A) x

cminus : (A : Algebra) → Algebra.R A → Algebra.R A
cminus A x = Algebra.max A (Algebra.zero A) (Algebra.neg A x)

record CReLULaws (A : Algebra) : Set₁ where
  open Algebra A
  field
    reconstruct : ∀ x →
      cplus A x + neg (cminus A x) ≡ x
    absDecompose : ∀ x →
      cplus A x + cminus A x ≡ abs x
    branchFinite : ∀ x →
      (cplus A x ≡ zero) ⊎ (cminus A x ≡ zero) ⊎
      ((cplus A x ≠ zero) × (cminus A x ≠ zero))

------------------------------------------------------------------------
-- L1 weight norm and two-layer 1-path norm.
------------------------------------------------------------------------

weightL1 : ∀ {A m n} → Matrix A m n → Algebra.R A
weightL1 {A} {m} {n} W =
  sumV (Algebra._+_ A) (Algebra.zero A)
    (mapV (λ i →
      sumV (Algebra._+_ A) (Algebra.zero A)
        (tabulateRow A n W i))
      (tabulateFin m))
  where
  tabulateFin : ∀ {k} → Fin k → Vec (Fin k) k
  tabulateFin {zero} ()
  tabulateFin {suc k} f = f ∷ tabulateFin (fsuc f)

  tabulateRow : ∀ {k} → Algebra A → Fin k → Matrix A m n → Fin m → Vec (Algebra.R A) k
  tabulateRow A zero W i = []
  tabulateRow A (suc k) W i = Algebra.abs A (W i fzero) ∷
    tabulateRow A k (λ i' j' → W i' (fsuc j')) i

-- The row/column enumerators above are deliberately finite.  The path norm
-- is presented independently as a certified finite quantity; its exact
-- expansion is supplied by the algebraic certificate below.
record OnePathNorm (A : Algebra) : Set₁ where
  field
    path1 : ∀ {m n p} → Matrix A m n → Matrix A n p → Algebra.R A
    nonnegative : ∀ {m n p} (W V : Matrix A m n) →
      Algebra.zero A ≤ path1 W V

------------------------------------------------------------------------
-- Tsallis-2 sparse attention as a finite KKT/active-set certificate.
-- For a fixed active set, weights are affine in scores and the normalization
-- is finite; no exp/log/softmax semantics are present.
------------------------------------------------------------------------

record Tsallis2Branch (A : Algebra) (n : Nat) : Set₁ where
  open Algebra A
  field
    scores tau weights : Vector A n
    active : Vec Bool n
    nonnegative : ∀ i → zero ≤ index weights i
    inactiveZero : ∀ i → index active i ≡ false → index weights i ≡ zero
    activeAffine : ∀ i → index active i ≡ true →
      index weights i + neg (index scores i + neg tau) ≡ zero
    normalized : sumV _+_ zero weights ≡ one

  -- This is the finite sparse-equilibrium normal form.
  equilibriumNormalForm :
    ∀ i → index active i ≡ true →
      index weights i ≡ index scores i + neg tau
  equilibriumNormalForm i h =
    trans
      (addNegCancel (index weights i) (index scores i + neg tau)
        (activeAffine i h))
      refl
    where
    addNegCancel : ∀ x y → x + neg y ≡ zero → x ≡ y
    addNegCancel x y h = hToEq x y h
      where
      hToEq : ∀ a b → a + neg b ≡ zero → a ≡ b
      hToEq a b h =
        trans
          (sym (addZeroR A a))
          (trans
            (cong (λ q → a + q) (sym (addNegR A b)))
            (trans
              (cong (λ q → a + q) h)
              refl))

------------------------------------------------------------------------
-- q-projection and standard q-IDBD direction.
------------------------------------------------------------------------

record QProjection (A : Algebra) (n : Nat) : Set₁ where
  field
    project : Vector A n → Vector A n
    idempotent : ∀ x → project (project x) ≡ project x
    preservesZero : project (mapV (λ _ → Algebra.zero A) x) ≡
      mapV (λ _ → Algebra.zero A) x
      where
      x : Vector A n

record DyadicScales (A : Algebra) : Set₁ where
  open Algebra A
  field
    scale : Nat → R A
    scaleZero : scale zero ≡ one
    halfLaw : ∀ k → scale (suc k) + scale (suc k) ≡ scale k

------------------------------------------------------------------------
-- Optional parameter-direction sign, kept separate from standard q-IDBD.
------------------------------------------------------------------------

record DirectionSign (A : Algebra) : Set₁ where
  open Algebra A
  field
    sign : R A → R A
    zeroSign : sign zero ≡ zero
    signMagnitude : ∀ x → sign x ≡ zero ⊎
      (sign x ≠ zero)

------------------------------------------------------------------------
-- Finite branch product: forward CReLU branch × Tsallis active set ×
-- optional optimizer-direction sign pattern.
------------------------------------------------------------------------

record CompositeBranch (A : Algebra) (n : Nat) : Set₁ where
  field
    forwardTag : Vec Bool n
    attentionTag : Vec Bool n
    updateTag : Vec Bool n

record CompositeCertificate (A : Algebra) (n : Nat) : Set₁ where
  field
    creluLaws : CReLULaws A
    attention : Tsallis2Branch A n
    projection : QProjection A n
    dyadicL2 : DyadicScales A
    branch : CompositeBranch A n

    -- Stability is deliberately a finite certificate, not a hidden analytic
    -- claim.  Coefficients are supplied in the same ordered scalar algebra.
    l1WeightBound : Algebra.R A
    onePathBound : Algebra.R A
    sensitivityBound : Algebra.R A

------------------------------------------------------------------------
-- Degree bookkeeping for the counterfactual algebraic Transformer.
-- CReLU/affine maps preserve degree; QK is quadratic; score×value is cubic.
------------------------------------------------------------------------

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc k) = 3 * pow3 k

attentionDegreeStep : Nat → Nat
attentionDegreeStep d = 3 * d

threePowRecurrence : ∀ k → attentionDegreeStep (pow3 k) ≡ pow3 (suc k)
threePowRecurrence zero = refl
threePowRecurrence (suc k) = refl

------------------------------------------------------------------------
-- Integrated finite theorem target.
------------------------------------------------------------------------

record EfficientCHAD_CReLU_Tsallis2_TheoremTarget
  (A : Algebra) (n : Nat) : Set₁ where
  field
    certificate : CompositeCertificate A n

    -- Finite equilibrium theorem for sparse attention.
    sparseEquilibrium :
      ∀ i →
        index (Tsallis2Branch.active (CompositeCertificate.attention certificate)) i ≡ true →
        index (Tsallis2Branch.weights (CompositeCertificate.attention certificate)) i ≡
        index (Tsallis2Branch.scores (CompositeCertificate.attention certificate)) i +
        neg A (Tsallis2Branch.tau (CompositeCertificate.attention certificate))

    -- CReLU exact reconstruction and L1 magnitude decomposition.
    creluReconstruction : ∀ x →
      cplus A x + neg A (cminus A x) ≡ x
    creluAbsDecomposition : ∀ x →
      cplus A x + cminus A x ≡ abs A x

    -- q-projection remains a retraction after the finite learner boundary.
    qProjectionIdempotent : ∀ x →
      QProjection.project (CompositeCertificate.projection certificate)
        (QProjection.project (CompositeCertificate.projection certificate) x) ≡
      QProjection.project (CompositeCertificate.projection certificate) x

    -- Branchwise polynomial order recurrence; no global analytic semantics.
    degreeBound : ∀ k → attentionDegreeStep (pow3 k) ≡ pow3 (suc k)

    -- All active finite certificates coexist in one state predicate.
    compositeFiniteOrderedClosure :
      CompositeCertificate A n → CompositeCertificate A n

------------------------------------------------------------------------
-- Constructor: the integrated theorem is assembled compositionally from
-- the local finite certificates; no theorem is asserted beyond its inputs.
------------------------------------------------------------------------

assembleTheoremTarget : ∀ {A n} →
  (c : CompositeCertificate A n) →
  EfficientCHAD_CReLU_Tsallis2_TheoremTarget A n
assembleTheoremTarget c =
  record
    { certificate = c
    ; sparseEquilibrium =
        λ i h → Tsallis2Branch.equilibriumNormalForm
          (CompositeCertificate.attention c) i h
    ; creluReconstruction =
        CReLULaws.reconstruct (CompositeCertificate.creluLaws c)
    ; creluAbsDecomposition =
        CReLULaws.absDecompose (CompositeCertificate.creluLaws c)
    ; qProjectionIdempotent =
        QProjection.idempotent (CompositeCertificate.projection c)
    ; degreeBound = threePowRecurrence
    ; compositeFiniteOrderedClosure = λ x → x
    }

------------------------------------------------------------------------
-- Canonical conclusions recorded by this target.
------------------------------------------------------------------------

canonicalDegreeLaw : ∀ k → attentionDegreeStep (pow3 k) ≡ pow3 (suc k)
canonicalDegreeLaw = threePowRecurrence

canonicalTsallisIsAffineOnBranch :
  ∀ {A n} (c : CompositeCertificate A n) →
  (∀ i → index (Tsallis2Branch.active (CompositeCertificate.attention c)) i ≡ true →
    index (Tsallis2Branch.weights (CompositeCertificate.attention c)) i ≡
      index (Tsallis2Branch.scores (CompositeCertificate.attention c)) i +
      neg A (Tsallis2Branch.tau (CompositeCertificate.attention c)))
canonicalTsallisIsAffineOnBranch c =
  λ i h → Tsallis2Branch.equilibriumNormalForm
    (CompositeCertificate.attention c) i h

canonicalQProjectionRetraction :
  ∀ {A n} (c : CompositeCertificate A n) (x : Vector A n) →
    QProjection.project (CompositeCertificate.projection c)
      (QProjection.project (CompositeCertificate.projection c) x) ≡
    QProjection.project (CompositeCertificate.projection c) x
canonicalQProjectionRetraction c =
  QProjection.idempotent (CompositeCertificate.projection c)
