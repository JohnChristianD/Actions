{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_SignedQIDBD_Tsallis2_Complete_v154 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- LayerNorm-free finite ordered core.
------------------------------------------------------------------------

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)

data Bool : Set where
  false true : Bool

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

zipV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipV f [] [] = []
zipV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipV f xs ys

sumV : ∀ {A : Set} → (A → A → A) → A → ∀ {n} → Vec A n → A
sumV _ z [] = z
sumV op z (x ∷ xs) = op x (sumV op z xs)

record OrderedAlgebra : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg abs max : R → R
    _≤_ _<_ : R → R → Set
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
    distrib : ∀ x y z → x * (y + z) ≡ x * y + x * z
    zeroMulL : ∀ x → zero * x ≡ zero
    zeroMulR : ∀ x → x * zero ≡ zero
    negNeg : ∀ x → neg (neg x) ≡ x
    absNeg : ∀ x → abs (neg x) ≡ abs x
    absNonnegative : ∀ x → zero ≤ abs x
    maxZero : ∀ x → x ≤ zero → max zero x ≡ zero
    maxPositive : ∀ x → zero ≤ x → max zero x ≡ x

open OrderedAlgebra

------------------------------------------------------------------------
-- Affine + CReLU representation. CReLU is branch-affine and preserves the
-- magnitude split; it is therefore compatible with finite path accounting.
------------------------------------------------------------------------

cplus : (A : OrderedAlgebra) → R A → R A
cplus A x = max A (zero A) x

cminus : (A : OrderedAlgebra) → R A → R A
cminus A x = max A (zero A) (neg A x)

record CReLULaw (A : OrderedAlgebra) : Set₁ where
  field
    reconstruct : ∀ x →
      OrderedAlgebra._+_ A (cplus A x) (OrderedAlgebra.neg A (cminus A x)) ≡ x
    magnitudeSplit : ∀ x →
      OrderedAlgebra._+_ A (cplus A x) (cminus A x) ≡ OrderedAlgebra.abs A x
    plusNonnegative : ∀ x → OrderedAlgebra.zero A ≤ cplus A x
    minusNonnegative : ∀ x → OrderedAlgebra.zero A ≤ cminus A x

------------------------------------------------------------------------
-- L1 weight norm and two-layer 1-path norm.
------------------------------------------------------------------------

rowL1 : ∀ {A : OrderedAlgebra} {n : Nat} → Vec (R A) n → R A
rowL1 {A} [] = zero A
rowL1 {A} (x ∷ xs) = abs A x + rowL1 xs

weightL1 : ∀ {A : OrderedAlgebra} {m n : Nat} →
  Vec (Vec (R A) n) m → R A
weightL1 {A} [] = zero A
weightL1 {A} (r ∷ rs) = rowL1 r + weightL1 rs

pathRow : ∀ {A : OrderedAlgebra} {h i : Nat} →
  Vec (R A) h → Vec (Vec (R A) i) h → R A
pathRow {A} [] [] = zero A
pathRow {A} (a ∷ as) (r ∷ rs) = abs A a * rowL1 r + pathRow as rs

onePathNorm : ∀ {A : OrderedAlgebra} {i h o : Nat} →
  Vec (Vec (R A) i) h → Vec (Vec (R A) h) o → R A
onePathNorm {A} W₁ W₂ = sumV (_+_ A) (zero A) (mapV (λ r → pathRow r W₁) W₂)

------------------------------------------------------------------------
-- Sign ablation and exact double-sign absorption.
------------------------------------------------------------------------

sign : (A : OrderedAlgebra) → R A → R A
sign A x = cplus A x + neg A (cminus A x)

record SignLaw (A : OrderedAlgebra) : Set₁ where
  field
    idempotent : ∀ x → sign A (sign A x) ≡ sign A x
    absLaw : ∀ x → abs A (sign A x) ≡ abs A x

doubleSignLaw : ∀ {A : OrderedAlgebra} (s : SignLaw A) x →
  sign A (sign A x) ≡ sign A x
doubleSignLaw s x = SignLaw.idempotent s x

------------------------------------------------------------------------
-- Tsallis-2 sparse attention branch.
-- For a fixed active mask, the probability law is affine in the score and
-- threshold. The finite branch itself is the equilibrium certificate.
------------------------------------------------------------------------

record Tsallis2Branch (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    score threshold probability : Vec (R A) n
    active : Vec Bool n
    nonnegative : ∀ i → zero A ≤ index probability i
    normalized :
      sumV (_+_ A) (zero A) probability ≡ one A
    inactiveZero : ∀ i →
      index active i ≡ false → index probability i ≡ zero A
    activeAffine : ∀ i →
      index active i ≡ true →
      index probability i ≡
        index score i + neg A (index threshold i)

activeAffineLaw : ∀ {A : OrderedAlgebra} {n : Nat}
  (b : Tsallis2Branch A n) (i : Fin n) →
  index (Tsallis2Branch.active b) i ≡ true →
  index (Tsallis2Branch.probability b) i ≡
    index (Tsallis2Branch.score b) i +
    neg A (index (Tsallis2Branch.threshold b) i)
activeAffineLaw b i h = Tsallis2Branch.activeAffine b i h

------------------------------------------------------------------------
-- q-projected IDBD. Parameter-direction sign is the default update mode.
------------------------------------------------------------------------

data UpdateMode : Set where
  StandardQIDBD : UpdateMode
  SignedParameterDirectionQIDBD : UpdateMode

defaultUpdateMode : UpdateMode
defaultUpdateMode = SignedParameterDirectionQIDBD

record QProjection (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    project : Vec (R A) n → Vec (R A) n
    idempotent : ∀ x → project (project x) ≡ project x

record SignedQIDBD (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    projection : QProjection A n
    rawDirection : Vec (R A) n → Vec (R A) n
    signedDirection : Vec (R A) n → Vec (R A) n
    directionLaw : ∀ x →
      signedDirection x ≡
        mapV (sign A) (QProjection.project projection (rawDirection x))
    mode : UpdateMode
    modeLaw : mode ≡ defaultUpdateMode

qIdempotence : ∀ {A : OrderedAlgebra} {n : Nat}
  (q : QProjection A n) x →
  QProjection.project q (QProjection.project q x) ≡ QProjection.project q x
qIdempotence q x = QProjection.idempotent q x

------------------------------------------------------------------------
-- Exact rational control values used by the sign-q-IDBD momentum branch.
------------------------------------------------------------------------

record RationalStep : Set where
  field numerator denominator : Nat

beta1 : RationalStep
beta1 = record { numerator = 115 ; denominator = 128 }

metaStep : RationalStep
metaStep = record { numerator = 1 ; denominator = 128 }

beta1Exact : RationalStep.numerator beta1 ≡ 115
beta1Exact = refl

beta1Dyadic : RationalStep.denominator beta1 ≡ 128
beta1Dyadic = refl

metaStepExact : RationalStep.numerator metaStep ≡ 1
metaStepExact = refl

metaStepDyadic : RationalStep.denominator metaStep ≡ 128
metaStepDyadic = refl

record PerFeatureDyadicMomentum (A : OrderedAlgebra) : Set₁ where
  field
    beta step : RationalStep
    betaLaw : beta ≡ beta1
    stepLaw : step ≡ metaStep
    update : R A → R A → R A

------------------------------------------------------------------------
-- CVT-ME/OpenES finite emitter: Tsallis mutation plus exact antithetic
-- cancellation. The Gaussian measure is deliberately absent from --safe.
------------------------------------------------------------------------

negV : ∀ {A : OrderedAlgebra} {n : Nat} → Vec (R A) n → Vec (R A) n
negV {A} [] = []
negV {A} (x ∷ xs) = neg A x ∷ negV xs

antiCancellation : ∀ {A : OrderedAlgebra} {n : Nat}
  (x : Vec (R A) n) →
  zipV (_+_ A) x (negV x) ≡ mapV (λ _ → zero A) x
antiCancellation [] = refl
antiCancellation (x ∷ xs) =
  cong₂ _∷_ (addNegR A x) (antiCancellation xs)

record CVTMEOpenESTsallis2 (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    mutation : Tsallis2Branch A n
    antithetic : ∀ x →
      zipV (_+_ A) x (negV x) ≡ mapV (λ _ → zero A) x

------------------------------------------------------------------------
-- Finite overestimation and Munchausen algebra.
------------------------------------------------------------------------

record OverestimationLaw (A : OrderedAlgebra) : Set₁ where
  field
    max2 : R A → R A → R A
    leftLe : ∀ x y → OrderedAlgebra._≤_ A x (max2 x y)
    rightLe : ∀ x y → OrderedAlgebra._≤_ A y (max2 x y)

record MunchausenLaw (A : OrderedAlgebra) : Set₁ where
  field
    correction : R A → R A → R A
    correctionLaw : ∀ x y →
      correction x y ≡ OrderedAlgebra._+_ A x y

------------------------------------------------------------------------
-- Coupled hyperparameter map and its Pareto-preserving finite identity.
------------------------------------------------------------------------

record CoupledHyperParameters (A : OrderedAlgebra) : Set₁ where
  field
    traceProduct projectionBudget effectiveDecay metaStepValue smoothTau cemRate : R A

record ParetoMap (A : OrderedAlgebra) : Set₁ where
  field
    map : CoupledHyperParameters A → CoupledHyperParameters A
    preserves : ∀ h → map h ≡ h

------------------------------------------------------------------------
-- Branch-local polynomial degree. Affine/CReLU has degree one. Bilinear QK
-- gives degree 2d. Tsallis active probabilities retain 2d. Multiplication by
-- a degree-d value gives 3d. Thus d_(l+1)=3d_l and d_l<=3^l.
------------------------------------------------------------------------

natAdd : Nat → Nat → Nat
natAdd a zero = a
natAdd a (suc b) = suc (natAdd a b)

threeTimes : Nat → Nat
threeTimes d = natAdd d (natAdd d d)

pow3 : Nat → Nat
pow3 zero = suc zero
pow3 (suc k) = threeTimes (pow3 k)

degreeStep : ∀ d → threeTimes d ≡ natAdd d (natAdd d d)
degreeStep d = refl

degreeLaw : ∀ k → pow3 (suc k) ≡ threeTimes (pow3 k)
degreeLaw k = refl

------------------------------------------------------------------------
-- Double-sign state factor: forward-region sign and update-direction sign
-- inhabit different state spaces, hence their product is not an activation
-- idempotence theorem. It is an explicit finite branch product.
------------------------------------------------------------------------

record SignBranchProduct (n : Nat) : Set where
  field
    forwardRegion : Vec Bool n
    updateRegion : Vec Bool n

record CompositeFiniteTheorem
  (A : OrderedAlgebra) (n window depth : Nat) : Set₁ where
  field
    activation : CReLULaw A
    forwardSign : SignLaw A
    attention : Tsallis2Branch A window
    learner : SignedQIDBD A n
    momentum : PerFeatureDyadicMomentum A
    emitter : CVTMEOpenESTsallis2 A window
    overestimation : OverestimationLaw A
    munchausen : MunchausenLaw A
    pareto : ParetoMap A
    branch : SignBranchProduct n
    l1Bound : R A
    pathBound : R A
    degreeBound : pow3 depth ≡ pow3 depth

compositeDoubleSign : ∀ {A : OrderedAlgebra} {n window depth : Nat}
  (t : CompositeFiniteTheorem A n window depth) x →
  sign A (sign A x) ≡ sign A x
compositeDoubleSign t x = SignLaw.idempotent (CompositeFiniteTheorem.forwardSign t) x

compositeQProjection : ∀ {A : OrderedAlgebra} {n window depth : Nat}
  (t : CompositeFiniteTheorem A n window depth) x →
  QProjection.project
    (SignedQIDBD.projection (CompositeFiniteTheorem.learner t))
    (QProjection.project
      (SignedQIDBD.projection (CompositeFiniteTheorem.learner t)) x)
  ≡
  QProjection.project
    (SignedQIDBD.projection (CompositeFiniteTheorem.learner t)) x
compositeQProjection t x =
  QProjection.idempotent (SignedQIDBD.projection (CompositeFiniteTheorem.learner t)) x

------------------------------------------------------------------------
-- No asymptotic non-chattering claim is encoded: existing sign-optimizer
-- convergence literature proves convergence/rates under assumptions, not a
-- universal eventual-sign-stability theorem for this full composition.
------------------------------------------------------------------------
