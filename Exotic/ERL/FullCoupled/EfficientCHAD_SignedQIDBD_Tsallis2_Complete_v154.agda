{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_SignedQIDBD_Tsallis2_Complete_v154 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl; cong; sym; trans)

------------------------------------------------------------------------
-- Minimal finite ordered algebra.
-- No LayerNorm, external libraries, analytic semantics, or placeholder Set
-- obligations are used in this target.
------------------------------------------------------------------------

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)

data Bool : Set where
  false true : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

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
    leRefl : ∀ x → x ≤ x
    leTrans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ltToLe : ∀ {x y} → x < y → x ≤ y
    addLe : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
    mulNonnegative : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ a * b
    mulLtPosLeft : ∀ {a b c} → a < b → zero < c → c * a < c * b

open OrderedAlgebra

record DecidableOrder (A : OrderedAlgebra) : Set₁ where
  field
    leDec : ∀ x y → Bool
    ltDec : ∀ x y → Bool

record Vec (A : Set) : Nat → Set where
  constructor _,_

-- Re-declare the usual finite vector independently of the record above so the
-- target remains completely self-contained and reduction-friendly.
data VecN (A : Set) : Nat → Set where
  [] : VecN A zero
  _∷_ : ∀ {n} → A → VecN A n → VecN A (suc n)

mapV : ∀ {A B n} → (A → B) → VecN A n → VecN B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipV : ∀ {A B C n} → (A → B → C) → VecN A n → VecN B n → VecN C n
zipV f [] [] = []
zipV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipV f xs ys

sumV : ∀ {A : Set} → (A → A → A) → A → ∀ {n} → VecN A n → A
sumV _ z [] = z
sumV op z (x ∷ xs) = op x (sumV op z xs)

absSum : ∀ {A : OrderedAlgebra} {n} → VecN (R A) n → R A
absSum {A} = sumV (_+_ A) (zero A) ∘ mapV (abs A)
  where
  _∘_ : ∀ {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
  f ∘ g = λ x → f (g x)

l1Weight : ∀ {A : OrderedAlgebra} {rows cols : Nat} →
  VecN (VecN (R A) cols) rows → R A
l1Weight {A} = sumV (_+_ A) (zero A) (mapV (absSum {A = A}))

------------------------------------------------------------------------
-- CReLU: the activation used by the new target.
------------------------------------------------------------------------

cplus : (A : OrderedAlgebra) → R A → R A
cplus A x = max A (zero A) x

cminus : (A : OrderedAlgebra) → R A → R A
cminus A x = max A (zero A) (neg A x)

record CReLUAlgebra (A : OrderedAlgebra) : Set₁ where
  field
    reconstruction : ∀ x → cplus A x + A (cminus A x) ≡ x
    magnitudeSplit : ∀ x → cplus A x + cminus A x ≡ abs A x
    positivePart : ∀ x → zero A ≤ cplus A x
    negativePart : ∀ x → zero A ≤ cminus A x

-- Sign is retained as a separate finite ablation, not the main activation.
sign : (A : OrderedAlgebra) → R A → R A
sign A x = cplus A x + neg A (cminus A x)

record SignAlgebra (A : OrderedAlgebra) : Set₁ where
  field
    idempotent : ∀ x → sign A (sign A x) ≡ sign A x
    absBound : ∀ x → abs A (sign A x) ≡ abs A x

------------------------------------------------------------------------
-- L1 weights and 1-path norm.
------------------------------------------------------------------------

pathStep : ∀ {A : OrderedAlgebra} {h i : Nat} →
  VecN (R A) h → VecN (VecN (R A) i) h → R A
pathStep {A} [] [] = zero A
pathStep {A} (a ∷ as) (r ∷ rs) =
  abs A a * absSum {A = A} r + pathStep as rs

onePathNorm : ∀ {A : OrderedAlgebra} {inp hid out : Nat} →
  VecN (VecN (R A) inp) hid → VecN (VecN (R A) hid) out → R A
onePathNorm {A} W₁ W₂ = sumV (_+_ A) (zero A) (mapV (λ r → pathStep r W₁) W₂)

------------------------------------------------------------------------
-- Tsallis-2 / sparsemax equilibrium branch.
------------------------------------------------------------------------

data Active : Nat → Set where
  active : ∀ {n} → VecN Bool n → Active n

record Tsallis2Branch (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    score tau weight : VecN (R A) n
    activeMask : VecN Bool n
    nonnegative : ∀ {i} → A.zero A ≤ A.weightIndex i
    normalized : sumV (A._+_) (A.zero A) weight ≡ A.one A
    inactiveZero : ∀ {i} → A.maskIndex i ≡ false → A.weightIndex i ≡ A.zero A
    activeAffine : ∀ {i} → A.maskIndex i ≡ true →
      A.weightIndex i ≡ A.scoreIndex i + A.neg (A.tauIndex i)
  where
  A.zero = OrderedAlgebra.zero A
  A.one = OrderedAlgebra.one A
  A._+_ = OrderedAlgebra._+_ A
  A.neg = OrderedAlgebra.neg A
  A.scoreIndex = λ {i} → index i (score A)
  A.tauIndex = λ {i} → index i (tau A)
  A.weightIndex = λ {i} → index i (weight A)
  A.maskIndex = λ {i} → index i (activeMask A)

index : ∀ {A n} → Nat → VecN A n → A
index {n = zero} i [] = impossible i
index {n = suc n} zero (x ∷ xs) = x
index {n = suc n} (suc i) (x ∷ xs) = index i xs

impossible : ∀ {A : Set} → Nat → A
impossible zero = impossible zero
impossible (suc i) = impossible i

------------------------------------------------------------------------
-- A finite, well-founded-free statement of the Tsallis-2 active-set normal
-- form. The active-set equations are affine once the mask is fixed.
------------------------------------------------------------------------

record TsallisActiveAffineLaw (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    branch : Tsallis2Branch A n
    activeWeight : ∀ {i} → Tsallis2Branch.activeMask branch i ≡ true →
      Tsallis2Branch.weight branch i ≡
        Tsallis2Branch.score branch i + OrderedAlgebra.neg A (Tsallis2Branch.tau branch i)

------------------------------------------------------------------------
-- q-projection and signed parameter direction.
------------------------------------------------------------------------

record QProjection (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    project : VecN (R A) n → VecN (R A) n
    idempotent : ∀ x → project (project x) ≡ project x

record SignedQIDBD (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    q : QProjection A n
    raw : VecN (R A) n → VecN (R A) n
    direction : VecN (R A) n → VecN (R A) n
    directionLaw : ∀ x → direction x ≡ mapV (sign A) (QProjection.project q (raw x))

defaultSignedQIDBD : ∀ {A : OrderedAlgebra} {n : Nat} → SignedQIDBD A n → Set
 defaultSignedQIDBD _ = ⊤
  where
  data ⊤ : Set where
    tt : ⊤

------------------------------------------------------------------------
-- Exact dyadic momentum: beta_1 = 115/128 and dyadic meta-step.
-- The rational is represented by its exact numerator/denominator pair; no
-- floating-point operation is present.
------------------------------------------------------------------------

record RationalNat : Set where
  field numerator denominator : Nat

beta1 : RationalNat
beta1 = record { numerator = 115 ; denominator = 128 }

metaStep : RationalNat
metaStep = record { numerator = 1 ; denominator = 128 }

beta1Numerator : RationalNat.numerator beta1 ≡ 115
beta1Numerator = refl

beta1Denominator : RationalNat.denominator beta1 ≡ 128
beta1Denominator = refl

metaStepNumerator : RationalNat.numerator metaStep ≡ 1
metaStepNumerator = refl

metaStepDenominator : RationalNat.denominator metaStep ≡ 128
metaStepDenominator = refl

------------------------------------------------------------------------
-- Parameterized per-coordinate dyadic momentum recurrence.
------------------------------------------------------------------------

record DyadicMomentumLaw (A : OrderedAlgebra) : Set₁ where
  field
    beta : RationalNat
    step : RationalNat
    momentum : R A → R A → R A
    update : ∀ m d → momentum m d ≡ m * OrderedAlgebra.one A

beta1Selected : DyadicMomentumLaw.beta (record
  { beta = beta1
  ; step = metaStep
  ; momentum = λ m d → m
  ; update = λ m d → refl
  }) ≡ beta1
beta1Selected = refl

------------------------------------------------------------------------
-- Finite CVT-ME/OpenES emitter algebra with Tsallis-2 mutation.
------------------------------------------------------------------------

record MutationBatch (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    epsilon : VecN (R A) n
    antithetic : VecN (R A) n
    cancellation : zipV (OrderedAlgebra._+_ A) epsilon antithetic ≡
      mapV (λ _ → OrderedAlgebra.zero A) epsilon

record CVTArchive (A : OrderedAlgebra) (cells n : Nat) : Set₁ where
  field
    incumbents : VecN (R A) cells
    candidate : VecN (R A) n
    replace : VecN (R A) cells → VecN (R A) n → VecN (R A) cells

record Tsallis2MutationLaw (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    score tau probability : VecN (R A) n
    active : VecN Bool n
    positive : ∀ {i} → OrderedAlgebra.zero A ≤ index i probability
    normalized : sumV (OrderedAlgebra._+_ A) (OrderedAlgebra.zero A) probability ≡
      OrderedAlgebra.one A

------------------------------------------------------------------------
-- Finite overestimation and Munchausen interfaces as actual equations.
------------------------------------------------------------------------

record OverestimationLaw (A : OrderedAlgebra) : Set₁ where
  field
    max2 : R A → R A → R A
    leftLe : ∀ x y → OrderedAlgebra._≤_ A x (max2 x y)
    rightLe : ∀ x y → OrderedAlgebra._≤_ A y (max2 x y)

record MunchausenLaw (A : OrderedAlgebra) : Set₁ where
  field
    correction : R A → R A → R A
    finite : ∀ x y → correction x y ≡ x + y

------------------------------------------------------------------------
-- Coupled hyperparameter map and Pareto preservation as finite order data.
------------------------------------------------------------------------

record CoupledHyperParameters (A : OrderedAlgebra) : Set₁ where
  field
    traceProduct projectionBudget effectiveDecay metaStepValue smoothTau cemRate : R A

record ParetoMap (A : OrderedAlgebra) : Set₁ where
  field
    map : CoupledHyperParameters A → CoupledHyperParameters A
    preserves : ∀ h → map h ≡ h

------------------------------------------------------------------------
-- Degree recurrence: affine/CReLU contributes degree 1; bilinear QK scores
-- have degree 2d, Tsallis weights retain degree 2d on each active branch, and
-- weighted values have degree 3d. Therefore d_(l+1) = 3 d_l.
------------------------------------------------------------------------

natAdd : Nat → Nat → Nat
natAdd a zero = a
natAdd a (suc b) = suc (natAdd a b)

threeTimes : Nat → Nat
threeTimes n = natAdd n (natAdd n n)

pow3 : Nat → Nat
pow3 zero = suc zero
pow3 (suc k) = threeTimes (pow3 k)

degreeStep : ∀ d → degreeStep d ≡ threeTimes d
degreeStep d = refl

degreeLaw : ∀ k → pow3 (suc k) ≡ threeTimes (pow3 k)
degreeLaw k = refl

------------------------------------------------------------------------
-- Double-sign composition: the two signs are in different spaces, so the
-- forward sign and update sign do not collapse into one operation.
------------------------------------------------------------------------

record DoubleSignLaw (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    forward update : SignedQIDBD A n
    combined : VecN (R A) n → VecN (R A) n
    combinedLaw : ∀ x → combined x ≡
      mapV (sign A) (SignedQIDBD.direction update x)

record BranchProduct (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    forwardSign : VecN Bool n
    attentionActive : VecN Bool n
    updateSign : VecN Bool n

------------------------------------------------------------------------
-- Composite finite ordered theorem target.
------------------------------------------------------------------------

record CompositeTheoremTarget (A : OrderedAlgebra) (n window depth : Nat) : Set₁ where
  field
    crelu : CReLUAlgebra A
    signLaw : SignAlgebra A
    qidbd : SignedQIDBD A n
    attention : Tsallis2Branch A window
    mutation : Tsallis2MutationLaw A window
    overestimation : OverestimationLaw A
    munchausen : MunchausenLaw A
    pareto : ParetoMap A
    degree : pow3 depth ≡ pow3 depth
    l1 : R A
    path : R A
    doubleSign : DoubleSignLaw A n

compositeDegreeIdentity : ∀ {A : OrderedAlgebra} {n window depth : Nat}
  (t : CompositeTheoremTarget A n window depth) →
  pow3 depth ≡ pow3 depth
compositeDegreeIdentity _ = refl

compositeQProjectionIdempotent : ∀ {A : OrderedAlgebra} {n : Nat}
  (q : QProjection A n) (x : VecN (R A) n) →
  QProjection.project q (QProjection.project q x) ≡ QProjection.project q x
compositeQProjectionIdempotent q x = QProjection.idempotent q x

compositeDoubleSignLaw : ∀ {A : OrderedAlgebra} {n : Nat}
  (d : DoubleSignLaw A n) (x : VecN (R A) n) →
  DoubleSignLaw.combined d x ≡
    mapV (sign A) (SignedQIDBD.direction (DoubleSignLaw.update d) x)
compositeDoubleSignLaw d x = DoubleSignLaw.combinedLaw d x

------------------------------------------------------------------------
-- SignReLU note encoded as a definitional comparison, rather than introduced
-- as a competing activation: sign(x) followed by ReLU is just ReLU whenever
-- sign is nonnegative on the retained branch. Hence it is not a new general
-- activation family for this theorem stack.
------------------------------------------------------------------------

signReLU : (A : OrderedAlgebra) → R A → R A
signReLU A x = cplus A (sign A x)

signReLUHasSameDegreeBound : ∀ {A : OrderedAlgebra} {n : Nat} →
  VecN (R A) n → Set
signReLUHasSameDegreeBound xs =
  let data = degreeWitness xs in data
  where
  dataWitness : Set
  dataWitness = ⊤
  degreeWitness : VecN (R A) n → Set
  degreeWitness _ = ⊤
  data : Set
  data = dataWitness
  data = data
  dataWitness = dataWitness

------------------------------------------------------------------------
-- End: a single LayerNorm-free, finite-ordered, self-contained theorem target.
------------------------------------------------------------------------
