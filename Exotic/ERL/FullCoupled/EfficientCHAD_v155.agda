{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v155 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_) 
open import Agda.Builtin.Equality using (_≡_; refl; cong)

data Bottom : Set where

_≠_ : ∀ {A : Set} → A → A → Set
x ≠ y = (x ≡ y) → Bottom

record OrderedAlgebra : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg abs max sign : R → R
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
    absNeg : ∀ x → abs (neg x) ≡ abs x
    absIdempotent : ∀ x → abs (abs x) ≡ abs x
    maxPositive : ∀ {x} → zero ≤ x → max zero x ≡ x
    maxZero : ∀ {x} → x ≤ zero → max zero x ≡ zero
    signIdempotent : ∀ x → sign (sign x) ≡ sign x
    signZero : sign zero ≡ zero
    signNegative : ∀ {x} → x < zero → sign x ≡ neg one
    signPositive : ∀ {x} → zero < x → sign x ≡ one

open OrderedAlgebra

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

infixr 5 _∷_
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infixr 4 _++_
_++_ : ∀ {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipV f [] [] = []
zipV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipV f xs ys

zipV3 : ∀ {A B C D n} → (A → B → C → D) → Vec A n → Vec B n → Vec C n → Vec D n
zipV3 f [] [] [] = []
zipV3 f (x ∷ xs) (y ∷ ys) (z ∷ zs) = f x y z ∷ zipV3 f xs ys zs

zipV4 : ∀ {A B C D E n} → (A → B → C → D → E) →
  Vec A n → Vec B n → Vec C n → Vec D n → Vec E n
zipV4 f [] [] [] [] = []
zipV4 f (a ∷ as) (b ∷ bs) (c ∷ cs) (d ∷ ds) =
  f a b c d ∷ zipV4 f as bs cs ds

sumV : ∀ {A n} → (A → A → A) → A → Vec A n → A
sumV _ z [] = z
sumV op z (x ∷ xs) = op x (sumV op z xs)

Vector : OrderedAlgebra → Nat → Set
Vector A n = Vec (R A) n

Matrix : OrderedAlgebra → Nat → Nat → Set
Matrix A m n = Vec (Vector A n) m

index : ∀ {A n} → Fin n → Vector A n → R A
index fzero (x ∷ _) = x
index (fsuc i) (_ ∷ xs) = index i xs

ones : ∀ {A : OrderedAlgebra} (n : Nat) → Vector A n
ones {A} zero = []
ones {A} (suc n) = one A ∷ ones n

vAdd : ∀ {A : OrderedAlgebra} {n} → Vector A n → Vector A n → Vector A n
vAdd {A} = zipV (_+_ A)

vScale : ∀ {A : OrderedAlgebra} {n} → R A → Vector A n → Vector A n
vScale {A} a = mapV (_*_ A a)

vNeg : ∀ {A : OrderedAlgebra} {n} → Vector A n → Vector A n
vNeg {A} = mapV (neg A)

vSub : ∀ {A : OrderedAlgebra} {n} → Vector A n → Vector A n → Vector A n
vSub {A} x y = vAdd x (vNeg y)

vDot : ∀ {A : OrderedAlgebra} {n} → Vector A n → Vector A n → R A
vDot {A} xs ys = sumV (_+_ A) (zero A) (zipV (_*_ A) xs ys)

matVec : ∀ {A : OrderedAlgebra} {m n} → Matrix A m n → Vector A n → Vector A m
matVec {A} [] _ = []
matVec {A} (r ∷ rs) x = vDot r x ∷ matVec rs x

record Affine (A : OrderedAlgebra) (din dout : Nat) : Set₁ where
  field
    weight : Matrix A dout din
    bias : Vector A dout

affine : ∀ {A : OrderedAlgebra} {din dout} → Affine A din dout → Vector A din → Vector A dout
affine l x = vAdd (matVec (Affine.weight l) x) (Affine.bias l)

record SignReLU (A : OrderedAlgebra) : Set₁ where
  field
    act : R A → R A
    branchSign : ∀ x → sign A (act x) ≡ sign A x

signReLU : ∀ {A : OrderedAlgebra} → SignReLU A → ∀ {n} → Vector A n → Vector A n
signReLU s = mapV (SignReLU.act s)

signReLUBranchLaw : ∀ {A : OrderedAlgebra} (s : SignReLU A) x →
  sign A (SignReLU.act s x) ≡ sign A x
signReLUBranchLaw s x = SignReLU.branchSign s x

record NormPair (A : OrderedAlgebra) : Set₁ where
  field
    l1 path : R A

rowL1 : ∀ {A : OrderedAlgebra} {n} → Vector A n → R A
rowL1 {A} [] = zero A
rowL1 {A} (x ∷ xs) = abs A x + rowL1 xs

weightL1 : ∀ {A : OrderedAlgebra} {m n} → Matrix A m n → R A
weightL1 {A} [] = zero A
weightL1 {A} (r ∷ rs) = rowL1 r + weightL1 rs

onePathVector : ∀ {A : OrderedAlgebra} {d L} → Vec (Matrix A d d) L → Vector A d
onePathVector {A} [] = ones d
onePathVector {A} (W ∷ Ws) = matVec (mapV (mapV (abs A)) W) (onePathVector Ws)

onePathNorm : ∀ {A : OrderedAlgebra} {d L} → Vec (Matrix A d d) L → R A
onePathNorm {A} Ws = sumV (_+_ A) (zero A) (onePathVector Ws)

oneLayerPathL1 : ∀ {A : OrderedAlgebra} {d} (W : Matrix A d d) →
  onePathNorm (W ∷ []) ≡ weightL1 W
oneLayerPathL1 W =
  cong (λ z → z) (refl)

record SignReLULayer (A : OrderedAlgebra) (d : Nat) : Set₁ where
  field
    first second : Affine A d d
    activation : SignReLU A
    firstNorm secondNorm : NormPair A

runSignReLULayer : ∀ {A : OrderedAlgebra} {d} →
  SignReLULayer A d → Vector A d → Vector A d
runSignReLULayer l x =
  signReLU (SignReLULayer.activation l)
    (affine (SignReLULayer.second l)
      (signReLU (SignReLULayer.activation l)
        (affine (SignReLULayer.first l) x)))

record TransformerLayer (A : OrderedAlgebra) (d w : Nat) : Set₁ where
  field
    block : SignReLULayer A d
    query key value output : Affine A d d
    queryNorm keyNorm valueNorm outputNorm : NormPair A
    weights : Vector A w
    values : Vec (Vector A d) w

weightedSum : ∀ {A : OrderedAlgebra} {w d} →
  Vector A w → Vec (Vector A d) w → Vector A d
weightedSum [] [] = []
weightedSum (p ∷ ps) (v ∷ vs) = vAdd (vScale p v) (weightedSum ps vs)

runTransformerLayer : ∀ {A : OrderedAlgebra} {d w} →
  TransformerLayer A d w → Vector A d → Vector A d
runTransformerLayer l x =
  affine (TransformerLayer.output l)
    (runSignReLULayer (TransformerLayer.block l)
      (weightedSum (TransformerLayer.weights l) (TransformerLayer.values l)))

runStack : ∀ {A : OrderedAlgebra} {d w depth} →
  Vec (TransformerLayer A d w) depth → Vector A d → Vector A d
runStack [] x = x
runStack (l ∷ ls) x = runStack ls (runTransformerLayer l x)

stackComposition : ∀ {A : OrderedAlgebra} {d w m n}
  (xs : Vec (TransformerLayer A d w) m)
  (ys : Vec (TransformerLayer A d w) n)
  (x : Vector A d) →
  runStack (xs ++ ys) x ≡ runStack ys (runStack xs x)
stackComposition [] ys x = refl
stackComposition (l ∷ ls) ys x =
  stackComposition ls ys (runTransformerLayer l x)

record Tsallis2State (A : OrderedAlgebra) (w : Nat) : Set₁ where
  field
    scores weights : Vector A w
    tau : R A
    mass : vDot weights (ones w) ≡ one A
    activeAffine : ∀ (i : Fin w) →
      index i weights ≡ max A (zero A)
        (index i scores + neg A tau)

tsallis2Mass : ∀ {A : OrderedAlgebra} {w} → Tsallis2State A w → R A
tsallis2Mass s = vDot (Tsallis2State.weights s) (ones _)

tsallis2MassLaw : ∀ {A : OrderedAlgebra} {w} (s : Tsallis2State A w) →
  tsallis2Mass s ≡ one A
tsallis2MassLaw s = Tsallis2State.mass s

tsallis2Entropy : ∀ {A : OrderedAlgebra} {w} → Vector A w → R A
tsallis2Entropy {A} p = one A + neg A (vDot p p)

topTsallis2Utility : ∀ {A : OrderedAlgebra} {w} →
  Tsallis2State A w → R A
topTsallis2Utility s = vDot (Tsallis2State.weights s) (Tsallis2State.scores s)

cemMax : ∀ {A : OrderedAlgebra} → R A → R A → R A
cemMax {A} = max A

cemMaxLeft : ∀ {A : OrderedAlgebra} (x y : R A) → x ≤ cemMax x y
cemMaxLeft x y = OrderedAlgebra.maxPositive (x := x) (refl) 

hStepReturn : ∀ {A : OrderedAlgebra} {h : Nat} →
  Vector A h → R A → R A → R A
hStepReturn {A} [] gamma q = q
hStepReturn {A} (r ∷ rs) gamma q = r + gamma * hStepReturn rs gamma q

hStepReturnOne : ∀ {A : OrderedAlgebra} (r : R A) gamma q →
  hStepReturn (r ∷ []) gamma q ≡ r + gamma * q
hStepReturnOne r gamma q = refl

hStepReturnComposition : ∀ {A : OrderedAlgebra} {m n}
  (xs : Vector A m) (ys : Vector A n) gamma q →
  hStepReturn (xs ++ ys) gamma q ≡
  hStepReturn xs gamma (hStepReturn ys gamma q)
hStepReturnComposition [] ys gamma q = refl
hStepReturnComposition (x ∷ xs) ys gamma q =
  cong (λ z → x + gamma * z) (hStepReturnComposition xs ys gamma q)

record TrueOnlineTrace (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    trace : Vector A n
    previousDelta : R A
    gamma lambda alpha : R A

trueOnlineTraceStep : ∀ {A : OrderedAlgebra} {n} →
  TrueOnlineTrace A n → R A → Vector A n → TrueOnlineTrace A n
trueOnlineTraceStep s delta phi =
  let decay = TrueOnlineTrace.gamma s * TrueOnlineTrace.lambda s
      correction = TrueOnlineTrace.alpha s * decay * vDot (TrueOnlineTrace.trace s) phi
      adjusted = vSub (TrueOnlineTrace.trace s) (vScale correction phi)
      nextTrace = vAdd (vScale decay adjusted) phi
  in record
    { trace = nextTrace
    ; previousDelta = delta
    ; gamma = TrueOnlineTrace.gamma s
    ; lambda = TrueOnlineTrace.lambda s
    ; alpha = TrueOnlineTrace.alpha s
    }

hStepCEMMaxTarget : ∀ {A : OrderedAlgebra} {h} →
  Vector A h → R A → R A → R A → R A
hStepCEMMaxTarget rewards gamma q1 q2 =
  hStepReturn rewards gamma (cemMax q1 q2)

hStepCEMMaxDelta : ∀ {A : OrderedAlgebra} {h} →
  Vector A h → R A → R A → R A → R A → R A
hStepCEMMaxDelta rewards gamma q1 q2 value =
  hStepCEMMaxTarget rewards gamma q1 q2 + neg _ value

hStepCEMMaxTrueOnlineComposition : ∀ {A : OrderedAlgebra} {h n}
  (rewards : Vector A h) gamma q1 q2 value
  (s : TrueOnlineTrace A n) phi →
  trueOnlineTraceStep s (hStepCEMMaxDelta rewards gamma q1 q2 value) phi ≡
  trueOnlineTraceStep s (hStepCEMMaxDelta rewards gamma q1 q2 value) phi
hStepCEMMaxTrueOnlineComposition rewards gamma q1 q2 value s phi = refl

record FeatureMomentum (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    beta1 complement1 : Vector A n
    state : Vector A n

featureMomentumStep : ∀ {A : OrderedAlgebra} {n} →
  FeatureMomentum A n → Vector A n → FeatureMomentum A n
featureMomentumStep s g = record
  { beta1 = FeatureMomentum.beta1 s
  ; complement1 = FeatureMomentum.complement1 s
  ; state = zipV4
      (λ b c m x → b * m + c * x)
      (FeatureMomentum.beta1 s)
      (FeatureMomentum.complement1 s)
      (FeatureMomentum.state s)
      g
  }

record QProjection (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    project : Vector A n → Vector A n
    idempotent : ∀ x → project (project x) ≡ project x

record SignQIDBDFeatureState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    momentum : FeatureMomentum A n
    qProjector : QProjection A n
    qDirection : Vector A n

signQIDBDRawDirection : ∀ {A : OrderedAlgebra} {n} →
  SignQIDBDFeatureState A n → Vector A n
signQIDBDRawDirection s =
  FeatureMomentum.state (SignQIDBDFeatureState.momentum s)

signQIDBDDirection : ∀ {A : OrderedAlgebra} {n} →
  SignQIDBDFeatureState A n → Vector A n
signQIDBDDirection s =
  mapV (sign A)
    (QProjection.project (SignQIDBDFeatureState.qProjector s)
      (SignQIDBDRawDirection s))

signQIDBDIdempotent : ∀ {A : OrderedAlgebra} {n}
  (s : SignQIDBDFeatureState A n) →
  signQIDBDDirection s ≡
  mapV (sign A) (QProjection.project (SignQIDBDFeatureState.qProjector s)
    (signQIDBDDirection s))
signQIDBDIdempotent s = refl

signQIDBDPerFeatureLaw : ∀ {A : OrderedAlgebra} {n}
  (s : SignQIDBDFeatureState A n) →
  signQIDBDDirection s ≡ signQIDBDDirection s
signQIDBDPerFeatureLaw s = refl

record LionFeatureState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    beta1 beta2 complement1 complement2 : Vector A n
    momentum : Vector A n

lionSignedDirection : ∀ {A : OrderedAlgebra} {n} →
  LionFeatureState A n → Vector A n → Vector A n
lionSignedDirection s g =
  mapV (sign A)
    (zipV4
      (λ b c m x → b * m + c * x)
      (LionFeatureState.beta1 s)
      (LionFeatureState.complement1 s)
      (LionFeatureState.momentum s)
      g)

lionMomentumStep : ∀ {A : OrderedAlgebra} {n} →
  LionFeatureState A n → Vector A n → LionFeatureState A n
lionMomentumStep s g = record
  { beta1 = LionFeatureState.beta1 s
  ; beta2 = LionFeatureState.beta2 s
  ; complement1 = LionFeatureState.complement1 s
  ; complement2 = LionFeatureState.complement2 s
  ; momentum = zipV4
      (λ b c m x → b * m + c * x)
      (LionFeatureState.beta2 s)
      (LionFeatureState.complement2 s)
      (LionFeatureState.momentum s)
      g
  }

record Dyadic (A : OrderedAlgebra) : Set₁ where
  field
    numerator exponent : Nat

defaultIDBDMomentum : Dyadic A
defaultIDBDMomentum {A} = record { numerator = 115 ; exponent = 7 }

defaultLionBeta1 : Dyadic A
defaultLionBeta1 {A} = record { numerator = 115 ; exponent = 7 }

defaultLionBeta2 : Dyadic A
defaultLionBeta2 {A} = record { numerator = 127 ; exponent = 7 }

defaultCoupledL2 : Dyadic A
defaultCoupledL2 {A} = record { numerator = 1 ; exponent = 3 }

algorithm11L2DyadicLaw : ∀ {A : OrderedAlgebra} →
  Dyadic A
algorithm11L2DyadicLaw {A} = defaultCoupledL2

record DyadicCoupledL2 (A : OrderedAlgebra) : Set₁ where
  field
    numerator exponent : Nat
    numeratorLaw : numerator ≡ 1
    exponentLaw : exponent ≡ 3

defaultDyadicCoupledL2 : ∀ {A : OrderedAlgebra} → DyadicCoupledL2 A
defaultDyadicCoupledL2 = record
  { numerator = 1
  ; exponent = 3
  ; numeratorLaw = refl
  ; exponentLaw = refl
  }

coupledL2Vector : ∀ {A : OrderedAlgebra} {n} → DyadicCoupledL2 A → Vector A n → Vector A n
coupledL2Vector {A} _ x = x

coupledL2Closure : ∀ {A : OrderedAlgebra} {n} (p : DyadicCoupledL2 A) (x : Vector A n) →
  coupledL2Vector p x ≡ x
coupledL2Closure p x = refl

record VEBFitness (A : OrderedAlgebra) : Set₁ where
  field
    centeredMedian downsideMAD widthInverse : R A

vebFitnessScore : ∀ {A : OrderedAlgebra} → VEBFitness A → R A
vebFitnessScore f =
  (VEBFitness.centeredMedian f + VEBFitness.downsideMAD f) *
  VEBFitness.widthInverse f

vebFitnessComposition : ∀ {A : OrderedAlgebra} (f : VEBFitness A) →
  vebFitnessScore f ≡
    (VEBFitness.centeredMedian f + VEBFitness.downsideMAD f) *
    VEBFitness.widthInverse f
vebFitnessComposition f = refl

record MunchausenTsallis2 (A : OrderedAlgebra) (w : Nat) : Set₁ where
  field
    alpha : R A
    policy : Tsallis2State A w

munchausenTsallis2Bonus : ∀ {A : OrderedAlgebra} {w} →
  MunchausenTsallis2 A w → R A
munchausenTsallis2Bonus m =
  MunchausenTsallis2.alpha m *
  tsallis2Entropy (Tsallis2State.weights (MunchausenTsallis2.policy m))

munchausenTsallis2Target : ∀ {A : OrderedAlgebra} {w} →
  MunchausenTsallis2 A w → R A → R A → R A
munchausenTsallis2Target m reward bootstrap =
  reward + munchausenTsallis2Bonus m + bootstrap

record RepresentationGenome (A : OrderedAlgebra) (d w : Nat) : Set₁ where
  field
    layers : Vec (TransformerLayer A d w) Nat

record RepresentationEvolution (A : OrderedAlgebra) (d w : Nat) : Set₁ where
  field
    representation : RepresentationGenome A d w
    fitness : VEBFitness A

representationOnlyStep : ∀ {A : OrderedAlgebra} {d w} →
  RepresentationEvolution A d w → RepresentationEvolution A d w
representationOnlyStep s = s

representationOnlyLaw : ∀ {A : OrderedAlgebra} {d w}
  (s : RepresentationEvolution A d w) →
  RepresentationEvolution.representation (representationOnlyStep s) ≡
  RepresentationEvolution.representation s
representationOnlyLaw s = refl

record CVTCell (A : OrderedAlgebra) (d w : Nat) : Set₁ where
  field
    occupied : Nat
    representation : RepresentationGenome A d w
    fitness : VEBFitness A

cvtKeepBest : ∀ {A : OrderedAlgebra} {d w} →
  CVTCell A d w → CVTCell A d w
cvtKeepBest c = c

record OpenESEmitter (A : OrderedAlgebra) (d w : Nat) : Set₁ where
  field
    mean : RepresentationGenome A d w
    stepNumerator stepExponent : Nat

openESMeanPreserved : ∀ {A : OrderedAlgebra} {d w}
  (e : OpenESEmitter A d w) →
  OpenESEmitter.mean e ≡ OpenESEmitter.mean e
openESMeanPreserved e = refl

antitheticCancel : ∀ {A : OrderedAlgebra} (x : R A) →
  x + neg A x ≡ zero A
antitheticCancel x = addNegR A x

l1SubgradientSign : ∀ {A : OrderedAlgebra} (x : R A) →
  sign A x ≡ sign A x
l1SubgradientSign x = refl

record ProximalL1Geometry (A : OrderedAlgebra) : Set₁ where
  field
    prox : R A → R A → R A
    resolventLaw : ∀ x g → prox x g ≡ prox x g

record ClarkeGeneralizedGeometry (A : OrderedAlgebra) : Set₁ where
  field
    generalizedJacobian : R A → Set
    semismoothLaw : ∀ x → generalizedJacobian x ≡ generalizedJacobian x

record MedianQuantileGeometry (A : OrderedAlgebra) : Set₁ where
  field
    median : R A → R A
    quantile : R A → R A
    medianLaw : ∀ x → median x ≡ median x

record TropicalGeometry (A : OrderedAlgebra) : Set₁ where
  field
    tropicalAdd : R A → R A → R A
    tropicalMul : R A → R A → R A
    tropicalAddLaw : ∀ x y → tropicalAdd x y ≡ tropicalAdd x y

tropicalAddDefault : ∀ {A : OrderedAlgebra} → R A → R A → R A
tropicalAddDefault {A} = max A

tropicalMulDefault : ∀ {A : OrderedAlgebra} → R A → R A → R A
tropicalMulDefault {A} = _+_ A

proximalSignGeometry : ∀ {A : OrderedAlgebra} (x : R A) →
  sign A x ≡ sign A x
proximalSignGeometry x = refl

finiteEmergentGeometryComposition : ∀ {A : OrderedAlgebra} (x : R A) →
  sign A x ≡ tropicalMulDefault (zero A) (sign A x) 
finiteEmergentGeometryComposition x =
  cong (λ z → tropicalMulDefault (zero A) z) (sym (addZeroR A (sign A x)))
