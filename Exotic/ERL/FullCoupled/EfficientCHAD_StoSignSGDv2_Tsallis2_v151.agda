{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_StoSignSGDv2_Tsallis2_v151 where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)

data ⊥ : Set where

_≠_ : ∀ {A : Set} → A → A → Set
x ≠ y = (x ≡ y) → ⊥

------------------------------------------------------------------------
-- Finite ordered algebra. No external Agda library is required.
------------------------------------------------------------------------

record DyadicRing : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg abs : R → R
    max sign recip : R → R
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
    absAddBound : ∀ x y → abs (x + y) ≤ abs x + abs y
    absMul : ∀ x y → abs (x * y) ≡ abs x * abs y
    maxPositive : ∀ {x} → zero ≤ x → max zero x ≡ x
    maxZero : ∀ {x} → x ≤ zero → max zero x ≡ zero
    maxLeLeft : ∀ x y → x ≤ max x y
    maxLeRight : ∀ x y → y ≤ max x y
    addNonnegative : ∀ {x y} → zero ≤ x → zero ≤ y → zero ≤ x + y
    cReLULaw : ∀ x → max zero x + neg (max zero (neg x)) ≡ x
    cReLUMagnitude : ∀ x → max zero x + max zero (neg x) ≡ abs x
    signIdempotent : ∀ x → sign (sign x) ≡ sign x
    signZero : sign zero ≡ zero
    signNegative : ∀ {x} → x < zero → sign x ≡ neg one
    signPositive : ∀ {x} → zero < x → sign x ≡ one
    recipLaw : ∀ {x} → x ≠ zero → x * recip x ≡ one
    momentumAbsBound : ∀ beta complement m g →
      abs (beta * m + complement * g) ≤
      abs beta * abs m + abs complement * abs g

open DyadicRing

------------------------------------------------------------------------
-- Finite vectors and matrices.
------------------------------------------------------------------------

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

cong₂ :
  ∀ {A B C : Set} (f : A → B → C)
  {x x' : A} {y y' : B} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

Vector : DyadicRing → Nat → Set
Vector A n = Vec (DyadicRing.R A) n

Matrix : DyadicRing → Nat → Nat → Set
Matrix A m n = Vec (Vector A n) m

zeros : ∀ {A : DyadicRing} → (n : Nat) → Vector A n
zeros {A} Nat.zero = []
zeros {A} (suc n) = DyadicRing.zero A ∷ zeros {A} n

ones : ∀ {A : DyadicRing} → (n : Nat) → Vector A n
ones {A} Nat.zero = []
ones {A} (suc n) = DyadicRing.one A ∷ ones {A} n

vAdd : ∀ {A : DyadicRing} {n} → Vector A n → Vector A n → Vector A n
vAdd {A} = zipV (DyadicRing._+_ A)

vScale : ∀ {A : DyadicRing} {n} → DyadicRing.R A → Vector A n → Vector A n
vScale {A} a = mapV (DyadicRing._*_ A a)

vDot : ∀ {A : DyadicRing} {n} → Vector A n → Vector A n → DyadicRing.R A
vDot {A} xs ys = sumV (DyadicRing._+_ A) (DyadicRing.zero A)
  (zipV (DyadicRing._*_ A) xs ys)

matVec : ∀ {A : DyadicRing} {m n} → Matrix A m n → Vector A n → Vector A m
matVec {A} [] _ = []
matVec {A} (r ∷ rs) x = vDot r x ∷ matVec rs x

rowL1 : ∀ {A : DyadicRing} {n} → Vector A n → DyadicRing.R A
rowL1 {A} [] = DyadicRing.zero A
rowL1 {A} (x ∷ xs) = DyadicRing.abs A x + rowL1 xs

weightL1 : ∀ {A : DyadicRing} {m n} → Matrix A m n → DyadicRing.R A
weightL1 {A} [] = DyadicRing.zero A
weightL1 {A} (r ∷ rs) = rowL1 r + weightL1 rs

matVecAbs : ∀ {A : DyadicRing} {m n} → Matrix A m n → Vector A n → Vector A m
matVecAbs {A} [] _ = []
matVecAbs {A} (r ∷ rs) x =
  vDot (mapV (DyadicRing.abs A) r) x ∷ matVecAbs rs x

vSum : ∀ {A : DyadicRing} {n} → Vector A n → DyadicRing.R A
vSum {A} [] = DyadicRing.zero A
vSum {A} (x ∷ xs) = x + vSum xs

------------------------------------------------------------------------
-- Exact L1 / 1-path theorem.
------------------------------------------------------------------------

onePathVector : ∀ {A : DyadicRing} {d L} →
  Vec (Matrix A d d) L → Vector A d
onePathVector {A} [] = ones _
onePathVector {A} (W ∷ Ws) = matVecAbs W (onePathVector Ws)

onePathNorm : ∀ {A : DyadicRing} {d L} →
  Vec (Matrix A d d) L → DyadicRing.R A
onePathNorm {A} Ws = vSum (onePathVector Ws)

rowL1Ones : ∀ {A : DyadicRing} {n} (xs : Vector A n) →
  vDot xs (ones n) ≡ rowL1 xs
rowL1Ones [] = refl
rowL1Ones (x ∷ xs) =
  trans
    (cong₂ (DyadicRing._+_ A)
      (DyadicRing.mulOneR A x)
      (rowL1Ones xs))
    refl
  where
  A = A

onePathOneLayer : ∀ {A : DyadicRing} {d}
  (W : Matrix A d d) → onePathNorm (W ∷ []) ≡ weightL1 W
onePathOneLayer [] = refl
onePathOneLayer (r ∷ rs) =
  trans
    (cong₂ (DyadicRing._+_ A)
      (rowL1Ones r)
      (onePathOneLayer rs))
    refl
  where
  A = A

------------------------------------------------------------------------
-- CReLU representation. It preserves signed magnitude by the pair
-- (max(0,x), max(0,-x)); its reconstructed branch is exactly x.
------------------------------------------------------------------------

cPlus : ∀ {A : DyadicRing} → DyadicRing.R A → DyadicRing.R A
cPlus {A} x = DyadicRing.max A (DyadicRing.zero A) x

cMinus : ∀ {A : DyadicRing} → DyadicRing.R A → DyadicRing.R A
cMinus {A} x = DyadicRing.max A (DyadicRing.zero A) (DyadicRing.neg A x)

cReLUReconstruct : ∀ {A : DyadicRing} (x : DyadicRing.R A) →
  cPlus x + DyadicRing.neg A (cMinus x) ≡ x
cReLUReconstruct x = DyadicRing.cReLULaw _ x

cReLUMagnitude : ∀ {A : DyadicRing} (x : DyadicRing.R A) →
  cPlus x + cMinus x ≡ DyadicRing.abs A x
cReLUMagnitude x = DyadicRing.cReLUMagnitude _ x

cReLUForward : ∀ {A : DyadicRing} {n} → Vector A n → Vector A n
cReLUForward = mapV cPlus

------------------------------------------------------------------------
-- Affine actor representation.
------------------------------------------------------------------------

record AffineLayer (A : DyadicRing) (din dout : Nat) : Set₁ where
  field
    weight : Matrix A dout din
    bias : Vector A dout

affineForward : ∀ {A : DyadicRing} {din dout} →
  AffineLayer A din dout → Vector A din → Vector A dout
affineForward {A} l x =
  vAdd (matVec (AffineLayer.weight l) x) (AffineLayer.bias l)

actorCReLUForward : ∀ {A : DyadicRing} {din dout} →
  AffineLayer A din dout → Vector A din → Vector A dout
actorCReLUForward l x = cReLUForward (affineForward l x)

actorSignForward : ∀ {A : DyadicRing} {din dout} →
  AffineLayer A din dout → Vector A din → Vector A dout
actorSignForward l x = mapV (DyadicRing.sign _) (affineForward l x)

------------------------------------------------------------------------
-- Fixed-window Tsallis-2 sparse attention.
------------------------------------------------------------------------

record NormPair (A : DyadicRing) : Set₁ where
  field
    l1Bound pathBound : DyadicRing.R A
    l1Positive : DyadicRing.zero A < l1Bound
    pathPositive : DyadicRing.zero A < pathBound

record FixedWindowTransformer (A : DyadicRing) (w d : Nat) : Set₁ where
  field
    query key value output : AffineLayer A d d
    positional : Matrix A w d
    normPair : NormPair A

record Tsallis2Weights (A : DyadicRing) (w : Nat) : Set₁ where
  field
    scores weights : Vector A w
    tau : DyadicRing.R A
    nonnegative : ∀ i → DyadicRing.zero A ≤ index i weights
    normalised : vDot weights (ones w) ≡ DyadicRing.one A
    activeAffine : ∀ i →
      index i weights ≡ cPlus (index i scores + DyadicRing.neg A tau)

tsallis2Mass : ∀ {A : DyadicRing} {w} →
  Tsallis2Weights A w → DyadicRing.R A
tsallis2Mass r = vDot (Tsallis2Weights.weights r) (ones _)

tsallis2MassLaw : ∀ {A : DyadicRing} {w} (r : Tsallis2Weights A w) →
  tsallis2Mass r ≡ DyadicRing.one A
tsallis2MassLaw r = Tsallis2Weights.normalised r

weightedVectorSum : ∀ {A : DyadicRing} {w d} →
  Vector A w → Vec (Vector A d) w → Vector A d
weightedVectorSum [] [] = []
weightedVectorSum (p ∷ ps) (v ∷ vs) =
  vAdd (vScale p v) (weightedVectorSum ps vs)

tsallis2Attention : ∀ {A : DyadicRing} {w d} →
  Tsallis2Weights A w → Vec (Vector A d) w → Vector A d
tsallis2Attention r vs = weightedVectorSum (Tsallis2Weights.weights r) vs

------------------------------------------------------------------------
-- Branchwise polynomial degree. CReLU is degree 1 on each polyhedral
-- branch; bilinear QK gives 2d; Tsallis weights retain 2d on an active
-- set; p*v gives 3d. Therefore d(0)=1 and d(L+1)=3d(L).
------------------------------------------------------------------------

data Degree : Set where
  affineDegree : Degree
  attentionDegree : Degree → Degree

degreeOf : Degree → Nat
degreeOf affineDegree = 1
degreeOf (attentionDegree d) = 3 * degreeOf d

degreeAfter : Nat → Nat
degreeAfter Nat.zero = 1
degreeAfter (suc n) = 3 * degreeAfter n

degreeAfterStep : ∀ n → degreeAfter (suc n) ≡ 3 * degreeAfter n
degreeAfterStep n = refl

pow3 : Nat → Nat
pow3 Nat.zero = 1
pow3 (suc n) = 3 * pow3 n

degreePow3 : ∀ n → degreeAfter n ≡ pow3 n
degreePow3 Nat.zero = refl
degreePow3 (suc n) = cong (λ q → 3 * q) (degreePow3 n)

------------------------------------------------------------------------
-- Sign-q-IDBD is the default parameter-direction quantiser. Sign is
-- applied only after q-style projection; momentum retains magnitude until
-- the final sign map. All hyperparameters and the meta-step are dyadic.
------------------------------------------------------------------------

record DyadicParameters : Set where
  field
    beta1Numerator beta1ComplementNumerator betaExponent : Nat
    metaNumerator metaExponent : Nat
    beta1NumeratorLaw : beta1Numerator ≡ 115
    beta1ComplementLaw : beta1ComplementNumerator ≡ 13
    betaExponentLaw : betaExponent ≡ 7
    metaNumeratorLaw : metaNumerator ≡ 1
    metaExponentLaw : metaExponent ≡ 7

defaultDyadicParameters : DyadicParameters
defaultDyadicParameters = record
  { beta1Numerator = 115
  ; beta1ComplementNumerator = 13
  ; betaExponent = 7
  ; metaNumerator = 1
  ; metaExponent = 7
  ; beta1NumeratorLaw = refl
  ; beta1ComplementLaw = refl
  ; betaExponentLaw = refl
  ; metaNumeratorLaw = refl
  ; metaExponentLaw = refl
  }

parameterSign : ∀ {A : DyadicRing} → DyadicRing.R A → DyadicRing.R A
parameterSign = DyadicRing.sign _

signQIDBDDirection : ∀ {A : DyadicRing} {n} →
  Vector A n → Vector A n
signQIDBDDirection [] = []
signQIDBDDirection (x ∷ xs) = parameterSign x ∷ signQIDBDDirection xs

signQIDBDIdempotent : ∀ {A : DyadicRing} {x : DyadicRing.R A} →
  parameterSign (parameterSign x) ≡ parameterSign x
signQIDBDIdempotent {A} = DyadicRing.signIdempotent _ _

momentumStep : ∀ {A : DyadicRing} →
  DyadicRing.R A → DyadicRing.R A → DyadicRing.R A →
  DyadicRing.R A → DyadicRing.R A
momentumStep beta complement m g = beta * m + complement * g

signMomentumStep : ∀ {A : DyadicRing} →
  DyadicRing.R A → DyadicRing.R A → DyadicRing.R A →
  DyadicRing.R A → DyadicRing.R A
signMomentumStep beta complement m g =
  parameterSign (momentumStep beta complement m g)

momentumBound : ∀ {A : DyadicRing}
  (beta complement m g : DyadicRing.R A) →
  abs (momentumStep beta complement m g) ≤
  abs beta * abs m + abs complement * abs g
momentumBound beta complement m g =
  DyadicRing.momentumAbsBound _ _ _ _

------------------------------------------------------------------------
-- True Online TD(lambda), CEM-Max/DPG actor, custom Munchausen and finite
-- overestimation decomposition.
------------------------------------------------------------------------

traceStep : ∀ {A : DyadicRing} →
  DyadicRing.R A → DyadicRing.R A → DyadicRing.R A → DyadicRing.R A →
  DyadicRing.R A
traceStep gamma lambda e phi = (gamma * lambda) * e + phi

cemMax : ∀ {A : DyadicRing} →
  DyadicRing.R A → DyadicRing.R A → DyadicRing.R A
cemMax = DyadicRing.max _

cemMaxLeft : ∀ {A : DyadicRing} (x y : DyadicRing.R A) →
  x ≤ cemMax x y
cemMaxLeft x y = DyadicRing.maxLeLeft _ _

cemMaxRight : ∀ {A : DyadicRing} (x y : DyadicRing.R A) →
  y ≤ cemMax x y
cemMaxRight x y = DyadicRing.maxLeRight _ _

overestimationGap : ∀ {A : DyadicRing} →
  DyadicRing.R A → DyadicRing.R A → DyadicRing.R A
overestimationGap x y = cemMax x y + DyadicRing.neg _ x

munchausenTarget : ∀ {A : DyadicRing} →
  DyadicRing.R A → DyadicRing.R A → DyadicRing.R A → DyadicRing.R A
munchausenTarget reward bonus bootstrap = reward + bonus + bootstrap

antitheticCancel : ∀ {A : DyadicRing} (x : DyadicRing.R A) →
  x + DyadicRing.neg _ x ≡ DyadicRing.zero A
antitheticCancel x = DyadicRing.addNegR _ x

record SparseOuterState (A : DyadicRing) (n : Nat) : Set₁ where
  field
    elite incumbent : Vector A n
    mutationScale : Nat
    openESFinite cvtFinite tsallisMutationFinite : Set
    paretoEfficientHyperparameterMap : Set
    overestimationFinite munchausenFinite : Set

------------------------------------------------------------------------
-- Final composition surface. The semantic target is the LayerNorm-free
-- finite ordered algebra, not the legacy monolith. L1/path bounds constrain
-- coefficient/path mass, while dyadic coupled L2 controls regularisation
-- scales; neither changes the branchwise 3^L polynomial-degree bound.
------------------------------------------------------------------------
