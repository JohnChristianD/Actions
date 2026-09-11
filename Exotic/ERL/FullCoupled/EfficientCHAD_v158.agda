{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v158 where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom : Set where

_≠_ : ∀ {A : Set} → A → A → Set
x ≠ y = x ≡ y → Bottom

cong₂ :
  ∀ {A B C : Set} (f : A → B → C)
  {x x' : A} {y y' : B} →
  x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

record OrderedAlgebra : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg abs : R → R
    max : R → R → R
    sign recip pow2 log2 : R → R
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
    recipZero : recip zero ≡ zero
    recipLaw : ∀ {x} → x ≠ zero → x * recip x ≡ one
    pow2Nonnegative : ∀ x → zero ≤ pow2 x
    log2Pow2 : ∀ x → log2 (pow2 x) ≡ x

open OrderedAlgebra

mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f [] = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

zipL : ∀ {A B C : Set} → (A → B → C) → List A → List B → List C
zipL f [] _ = []
zipL f (_ ∷ _) [] = []
zipL f (x ∷ xs) (y ∷ ys) = f x y ∷ zipL f xs ys

zipL4 : ∀ {A B C D E : Set} →
  (A → B → C → D → E) → List A → List B → List C → List D → List E
zipL4 f [] _ _ _ = []
zipL4 f (_ ∷ _) [] _ _ = []
zipL4 f (_ ∷ _) (_ ∷ _) [] _ = []
zipL4 f (_ ∷ _) (_ ∷ _) (_ ∷ _) [] = []
zipL4 f (a ∷ as) (b ∷ bs) (c ∷ cs) (d ∷ ds) = f a b c d ∷ zipL4 f as bs cs ds

sumL : ∀ {A : Set} → (A → A → A) → A → List A → A
sumL _ z [] = z
sumL op z (x ∷ xs) = op x (sumL op z xs)

FeatureVec : OrderedAlgebra → Set
FeatureVec A = List (R A)

featureDot : ∀ {A : OrderedAlgebra} → FeatureVec A → FeatureVec A → R A
featureDot {A} xs ys = sumL (_+_ A) (zero A) (zipL (_*_ A) xs ys)

featureScale : ∀ {A : OrderedAlgebra} → R A → FeatureVec A → FeatureVec A
featureScale {A} a = mapL (_*_ A a)

featureAdd : ∀ {A : OrderedAlgebra} → FeatureVec A → FeatureVec A → FeatureVec A
featureAdd {A} = zipL (_+_ A)

featureAbsSum : ∀ {A : OrderedAlgebra} → FeatureVec A → R A
featureAbsSum {A} [] = zero A
featureAbsSum {A} (x ∷ xs) = abs A x + featureAbsSum xs

weightL1 : ∀ {A : OrderedAlgebra} → List (FeatureVec A) → R A
weightL1 {A} [] = zero A
weightL1 {A} (x ∷ xs) = featureAbsSum x + weightL1 xs

pathProduct : ∀ {A : OrderedAlgebra} → List (FeatureVec A) → R A
pathProduct {A} [] = one A
pathProduct {A} (x ∷ xs) = featureAbsSum x * pathProduct xs

onePathNorm : ∀ {A : OrderedAlgebra} → List (FeatureVec A) → R A
onePathNorm = pathProduct

record NormPair (A : OrderedAlgebra) : Set₁ where
  field l1 path : R A

record Affine (A : OrderedAlgebra) : Set₁ where
  field apply : FeatureVec A → FeatureVec A

record SignReLU (A : OrderedAlgebra) : Set₁ where
  field act : R A → R A
        branchSign : ∀ x → sign A (act x) ≡ sign A x

signReLU : ∀ {A : OrderedAlgebra} → SignReLU A → FeatureVec A → FeatureVec A
signReLU s = mapL (SignReLU.act s)

record SignReLULayer (A : OrderedAlgebra) : Set₁ where
  field first second : Affine A
        activation : SignReLU A
        firstNorm secondNorm : NormPair A

runSignReLULayer : ∀ {A : OrderedAlgebra} → SignReLULayer A → FeatureVec A → FeatureVec A
runSignReLULayer l x = signReLU (SignReLULayer.activation l)
  (Affine.apply (SignReLULayer.second l)
    (signReLU (SignReLULayer.activation l)
      (Affine.apply (SignReLULayer.first l) x)))

twoAffineSignReLULaw : ∀ {A : OrderedAlgebra} (l : SignReLULayer A) x →
  runSignReLULayer l x ≡
  signReLU (SignReLULayer.activation l)
    (Affine.apply (SignReLULayer.second l)
      (signReLU (SignReLULayer.activation l)
        (Affine.apply (SignReLULayer.first l) x)))
twoAffineSignReLULaw l x = refl

qLog2 : ∀ {A : OrderedAlgebra} → R A → R A
qLog2 {A} x = one A + neg A (recip A x)

record Tsallis2State (A : OrderedAlgebra) : Set₁ where
  field scores weights : FeatureVec A
        tau : R A
        mass : featureDot weights (mapL (λ _ → one A) scores) ≡ one A
        sparseLaw : ∀ x → max A zero (x + neg A tau) ≡ max A zero (x + neg A tau)

record MunchausenTsallis2 (A : OrderedAlgebra) : Set₁ where
  field alpha policyValue : R A

munchausenAlphaQLog2 : ∀ {A : OrderedAlgebra} → MunchausenTsallis2 A → R A
munchausenAlphaQLog2 p = MunchausenTsallis2.alpha p * qLog2 (MunchausenTsallis2.policyValue p)

munchausenTsallis2Target : ∀ {A : OrderedAlgebra} → MunchausenTsallis2 A → R A → R A → R A
munchausenTsallis2Target p reward bootstrap =
  (reward + munchausenAlphaQLog2 p) + bootstrap

munchausenTsallis2CompositionLaw : ∀ {A : OrderedAlgebra}
  (p : MunchausenTsallis2 A) reward bootstrap →
  munchausenTsallis2Target p reward bootstrap ≡
    (reward + munchausenAlphaQLog2 p) + bootstrap
munchausenTsallis2CompositionLaw p reward bootstrap = refl

record TransformerLayer (A : OrderedAlgebra) : Set₁ where
  field representation : SignReLULayer A
        output : Affine A
        attention : Tsallis2State A
        values : List (FeatureVec A)

weightedSum : ∀ {A : OrderedAlgebra} → FeatureVec A → List (FeatureVec A) → FeatureVec A
weightedSum [] _ = []
weightedSum (_ ∷ _) [] = []
weightedSum (p ∷ ps) (v ∷ vs) = featureAdd (featureScale p v) (weightedSum ps vs)

runTransformerLayer : ∀ {A : OrderedAlgebra} → TransformerLayer A → FeatureVec A → FeatureVec A
runTransformerLayer l x = Affine.apply (TransformerLayer.output l)
  (runSignReLULayer (TransformerLayer.representation l)
    (weightedSum (Tsallis2State.weights (TransformerLayer.attention l))
      (TransformerLayer.values l)))

data Stack (A : OrderedAlgebra) : Set₁ where
  empty : Stack A
  push : TransformerLayer A → Stack A → Stack A

appendStack : ∀ {A : OrderedAlgebra} → Stack A → Stack A → Stack A
appendStack empty ys = ys
appendStack (push x xs) ys = push x (appendStack xs ys)

runStack : ∀ {A : OrderedAlgebra} → Stack A → FeatureVec A → FeatureVec A
runStack empty x = x
runStack (push l ls) x = runStack ls (runTransformerLayer l x)

stackComposition : ∀ {A : OrderedAlgebra} (xs ys : Stack A) x →
  runStack (appendStack xs ys) x ≡ runStack ys (runStack xs x)
stackComposition empty ys x = refl
stackComposition (push l xs) ys x = stackComposition xs ys (runTransformerLayer l x)

hStepReturn : ∀ {A : OrderedAlgebra} → List (R A) → R A → R A → R A
hStepReturn {A} [] gamma bootstrap = bootstrap
hStepReturn {A} (r ∷ rs) gamma bootstrap = r + gamma * hStepReturn rs gamma bootstrap

hStepOne : ∀ {A : OrderedAlgebra} (r gamma bootstrap : R A) →
  hStepReturn (r ∷ []) gamma bootstrap ≡ r + (gamma * bootstrap)
hStepOne r gamma bootstrap = refl

hStepRecursionLaw : ∀ {A : OrderedAlgebra} r gamma bootstrap (rs : List (R A)) →
  hStepReturn (r ∷ rs) gamma bootstrap ≡
  r + (gamma * hStepReturn rs gamma bootstrap)
hStepRecursionLaw r gamma bootstrap rs = refl

cemMax : ∀ {A : OrderedAlgebra} → R A → R A → R A
cemMax {A} = max A

hStepCEMMaxTarget : ∀ {A : OrderedAlgebra} → List (R A) → R A → R A → R A → R A
hStepCEMMaxTarget rewards gamma q₁ q₂ = hStepReturn rewards gamma (cemMax q₁ q₂)

record TrueOnlineTrace (A : OrderedAlgebra) : Set₁ where
  field trace : FeatureVec A
        previousDelta gamma lambda alpha : R A

trueOnlineTraceStep : ∀ {A : OrderedAlgebra} → TrueOnlineTrace A → R A → FeatureVec A → TrueOnlineTrace A
trueOnlineTraceStep s delta phi =
  let decay = TrueOnlineTrace.gamma s * TrueOnlineTrace.lambda s
      correction = (TrueOnlineTrace.alpha s * decay) * featureDot (TrueOnlineTrace.trace s) phi
      adjusted = featureAdd (TrueOnlineTrace.trace s) (mapL (neg A) (featureScale correction phi))
      nextTrace = featureAdd (featureScale decay adjusted) phi
  in record { trace = nextTrace
            ; previousDelta = delta
            ; gamma = TrueOnlineTrace.gamma s
            ; lambda = TrueOnlineTrace.lambda s
            ; alpha = TrueOnlineTrace.alpha s }

hStepCEMMaxDelta : ∀ {A : OrderedAlgebra} → List (R A) → R A → R A → R A → R A → R A
hStepCEMMaxDelta rewards gamma q₁ q₂ value = hStepCEMMaxTarget rewards gamma q₁ q₂ + neg _ value

hStepCEMMaxTrueOnline : ∀ {A : OrderedAlgebra} (rewards : List (R A)) gamma q₁ q₂ value (s : TrueOnlineTrace A) phi → TrueOnlineTrace A
hStepCEMMaxTrueOnline rewards gamma q₁ q₂ value s phi =
  trueOnlineTraceStep s (hStepCEMMaxDelta rewards gamma q₁ q₂ value) phi

hStepCEMMaxTrueOnlineLaw : ∀ {A : OrderedAlgebra} rewards gamma q₁ q₂ value (s : TrueOnlineTrace A) phi →
  hStepCEMMaxTrueOnline rewards gamma q₁ q₂ value s phi ≡
  trueOnlineTraceStep s (hStepCEMMaxDelta rewards gamma q₁ q₂ value) phi
hStepCEMMaxTrueOnlineLaw rewards gamma q₁ q₂ value s phi = refl

record FeatureMomentum (A : OrderedAlgebra) : Set₁ where
  field beta1 complement1 state : FeatureVec A

featureMomentumStep : ∀ {A : OrderedAlgebra} → FeatureMomentum A → FeatureVec A → FeatureMomentum A
featureMomentumStep s g = record
  { beta1 = FeatureMomentum.beta1 s
  ; complement1 = FeatureMomentum.complement1 s
  ; state = zipL4 (λ b c m x → (b * m) + (c * x))
      (FeatureMomentum.beta1 s) (FeatureMomentum.complement1 s)
      (FeatureMomentum.state s) g }

record QProjection (A : OrderedAlgebra) : Set₁ where
  field project : FeatureVec A → FeatureVec A
        idempotent : ∀ x → project (project x) ≡ project x

signQProjectionLaw : ∀ {A : OrderedAlgebra} (q : QProjection A) x →
  QProjection.project q (QProjection.project q x) ≡ QProjection.project q x
signQProjectionLaw q x = QProjection.idempotent q x

record SignQIDBDState (A : OrderedAlgebra) : Set₁ where
  field momentum : FeatureMomentum A
        qProjection : QProjection A
        beta alpha : FeatureVec A
        alphaFromBeta : alpha ≡ mapL (pow2 A) beta

idbdPow2 : ∀ {A : OrderedAlgebra} → FeatureVec A → FeatureVec A
idbdPow2 {A} = mapL (pow2 A)

idbdLog2 : ∀ {A : OrderedAlgebra} → FeatureVec A → FeatureVec A
idbdLog2 {A} = mapL (log2 A)

idbdBase2RoundTrip : ∀ {A : OrderedAlgebra} (xs : FeatureVec A) →
  idbdLog2 A (idbdPow2 A xs) ≡ xs
idbdBase2RoundTrip {A} [] = refl
idbdBase2RoundTrip {A} (x ∷ xs) =
  cong₂ _∷_ (log2Pow2 A x) (idbdBase2RoundTrip xs)

idbdAlphaDefinitionLaw : ∀ {A : OrderedAlgebra}
  (s : SignQIDBDState A) →
  SignQIDBDState.alpha s ≡ idbdPow2 A (SignQIDBDState.beta s)
idbdAlphaDefinitionLaw s = SignQIDBDState.alphaFromBeta s

idbdAlphaNonnegative : ∀ {A : OrderedAlgebra} (xs : FeatureVec A) →
  NonnegativeVec A (idbdPow2 A xs)
idbdAlphaNonnegative [] = nnNil
idbdAlphaNonnegative (x ∷ xs) = nnCons (pow2Nonnegative _ x) (idbdAlphaNonnegative xs)

record LionFeatureState (A : OrderedAlgebra) : Set₁ where
  field beta1 beta2 complement1 complement2 momentum : FeatureVec A

lionMomentumStep : ∀ {A : OrderedAlgebra} → LionFeatureState A → FeatureVec A → LionFeatureState A
lionMomentumStep s g = record
  { beta1 = LionFeatureState.beta1 s
  ; beta2 = LionFeatureState.beta2 s
  ; complement1 = LionFeatureState.complement1 s
  ; complement2 = LionFeatureState.complement2 s
  ; momentum = zipL4 (λ b c m x → (b * m) + (c * x))
      (LionFeatureState.beta2 s) (LionFeatureState.complement2 s)
      (LionFeatureState.momentum s) g }

lionDirection : ∀ {A : OrderedAlgebra} → LionFeatureState A → FeatureVec A → FeatureVec A
lionDirection s g = mapL (sign A)
  (zipL4 (λ b c m x → (b * m) + (c * x))
    (LionFeatureState.beta1 s) (LionFeatureState.complement1 s)
    (LionFeatureState.momentum s) g)

lionPerFeatureDirectionLaw : ∀ {A : OrderedAlgebra} (s : LionFeatureState A) g →
  lionDirection s g ≡
  mapL (sign A)
    (zipL4 (λ b c m x → (b * m) + (c * x))
      (LionFeatureState.beta1 s) (LionFeatureState.complement1 s)
      (LionFeatureState.momentum s) g)
lionPerFeatureDirectionLaw s g = refl

signQIDBDDirection : ∀ {A : OrderedAlgebra} → SignQIDBDState A → FeatureVec A
signQIDBDDirection s = mapL (sign A)
  (QProjection.project (SignQIDBDState.qProjection s)
    (FeatureMomentum.state (SignQIDBDState.momentum s)))

signQIDBDSignIdempotent : ∀ {A : OrderedAlgebra} x →
  sign A (sign A x) ≡ sign A x
signQIDBDSignIdempotent {A} x = signIdempotent A x

signDirectionIdempotent : ∀ {A : OrderedAlgebra} (xs : FeatureVec A) →
  mapL (sign A) (mapL (sign A) xs) ≡ mapL (sign A) xs
signDirectionIdempotent {A} [] = refl
signDirectionIdempotent {A} (x ∷ xs) =
  cong₂ _∷_ (signIdempotent A x) (signDirectionIdempotent xs)

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

coupledL2ZeroLaw : ∀ {A : OrderedAlgebra} (p : DyadicCoupledL2 A) →
  DyadicCoupledL2.lambda p ≡ zero A →
  coupledL2Penalty p (one A) ≡ zero A
coupledL2ZeroLaw p h =
  trans
    (cong (λ z → z * one A) h)
    (mulOneR A (zero A))

record VEBFitness (A : OrderedAlgebra) : Set₁ where
  field centeredMedian downsideMAD widthInverse : R A

vebFitnessScore : ∀ {A : OrderedAlgebra} → VEBFitness A → R A
vebFitnessScore f =
  (VEBFitness.centeredMedian f + VEBFitness.downsideMAD f) *
    VEBFitness.widthInverse f

record RepresentationGenome (A : OrderedAlgebra) : Set₁ where
  field stack : Stack A

record RepresentationCandidate (A : OrderedAlgebra) : Set₁ where
  field representation : RepresentationGenome A
        fitness : VEBFitness A

record RepresentationOnlyState (A : OrderedAlgebra) : Set₁ where
  field representation : RepresentationGenome A
        candidate : RepresentationCandidate A

onlyRepresentationEvolved : ∀ {A : OrderedAlgebra} →
  RepresentationOnlyState A → RepresentationGenome A
onlyRepresentationEvolved s = RepresentationOnlyState.representation s

representationOnlyLaw : ∀ {A : OrderedAlgebra} (s : RepresentationOnlyState A) →
  onlyRepresentationEvolved s ≡ RepresentationOnlyState.representation s
representationOnlyLaw s = refl

record CVTCell (A : OrderedAlgebra) : Set₁ where
  field candidate : RepresentationCandidate A

record OpenESEmitter (A : OrderedAlgebra) : Set₁ where
  field mean : RepresentationGenome A
        step : DyadicCode

antitheticCancel : ∀ {A : OrderedAlgebra} (x : R A) →
  x + neg A x ≡ zero A
antitheticCancel x = addNegR A x

antitheticFeatureCancel : ∀ {A : OrderedAlgebra} (xs : FeatureVec A) →
  featureAdd xs (mapL (neg A) xs) ≡
  mapL (λ _ → zero A) xs
antitheticFeatureCancel {A} [] = refl
antitheticFeatureCancel {A} (x ∷ xs) =
  cong₂ _∷_
    (addNegR A x)
    (antitheticFeatureCancel xs)

proximalSignLaw : ∀ {A : OrderedAlgebra} x →
  sign A (sign A x) ≡ sign A x
proximalSignLaw {A} x = signIdempotent A x

clarkeBranchLaw : ∀ {A : OrderedAlgebra} x →
  sign A (sign A x) ≡ sign A x
clarkeBranchLaw {A} x = signIdempotent A x

medianL1Law : ∀ {A : OrderedAlgebra} x →
  abs A (abs A x) ≡ abs A x
medianL1Law {A} x = absIdempotent A x

tropicalMaxLaw : ∀ {A : OrderedAlgebra} x y →
  x ≤ max A x y
tropicalMaxLaw {A} x y = maxLeLeft A x y

record EmergentGeometryLaw (A : OrderedAlgebra) (x : R A) : Set₁ where
  field
    proximal : sign A (sign A x) ≡ sign A x
    clarke : sign A (sign A x) ≡ sign A x
    median : abs A (abs A x) ≡ abs A x
    tropical : ∀ y → x ≤ max A x y

emergentGeometryLaw : ∀ (A : OrderedAlgebra) (x : R A) →
  EmergentGeometryLaw A x
emergentGeometryLaw A x = record
  { proximal = proximalSignLaw x
  ; clarke = clarkeBranchLaw x
  ; median = medianL1Law x
  ; tropical = tropicalMaxLaw x
  }

record FullFiniteOrderedRationalLearner (A : OrderedAlgebra) : Set₁ where
  field
    representation : RepresentationGenome A
    qState : SignQIDBDState A
    lionState : LionFeatureState A
    l2 : DyadicCoupledL2 A
    fitness : VEBFitness A
    emitter : OpenESEmitter A
    cvtCell : CVTCell A
    transformer : TransformerLayer A
    munchausen : MunchausenTsallis2 A
    trace : TrueOnlineTrace A
    hStepRewards : List (R A)

fullLearnerRepresentationLaw : ∀ {A : OrderedAlgebra}
  (s : FullFiniteOrderedRationalLearner A) x →
  runStack
    (RepresentationGenome.stack (FullFiniteOrderedRationalLearner.representation s)) x ≡
  runStack
    (RepresentationGenome.stack (FullFiniteOrderedRationalLearner.representation s)) x
fullLearnerRepresentationLaw s x = refl

fullLearnerHStepCEMLaw : ∀ {A : OrderedAlgebra}
  (s : FullFiniteOrderedRationalLearner A) gamma q₁ q₂ →
  hStepAndCEMMax
    (FullFiniteOrderedRationalLearner.hStepRewards s) gamma q₁ q₂ ≡
  hStepCEMMaxTarget
    (FullFiniteOrderedRationalLearner.hStepRewards s) gamma q₁ q₂
fullLearnerHStepCEMLaw s gamma q₁ q₂ = refl

hStepAndCEMMax : ∀ {A : OrderedAlgebra} → List (R A) → R A → R A → R A → R A
hStepAndCEMMax rewards gamma q₁ q₂ = hStepCEMMaxTarget rewards gamma q₁ q₂

hStepAndCEMMaxStateLaw : ∀ {A : OrderedAlgebra}
  (s : FullFiniteOrderedRationalLearner A) q₁ q₂ gamma → R A
hStepAndCEMMaxStateLaw s q₁ q₂ gamma =
  hStepAndCEMMax (FullFiniteOrderedRationalLearner.hStepRewards s) gamma q₁ q₂

record EfficientCHADState (A : OrderedAlgebra) : Set₁ where
  field representation : RepresentationGenome A
        qState : SignQIDBDState A
        lionState : LionFeatureState A
        l2 : DyadicCoupledL2 A
        fitness : VEBFitness A
        emitter : OpenESEmitter A
        cvtCell : CVTCell A
        hStepRewards : List (R A)

hStepAndCEMMaxCompatible : ∀ {A : OrderedAlgebra}
  (s : EfficientCHADState A) q₁ q₂ gamma → R A
hStepAndCEMMaxCompatible s q₁ q₂ gamma =
  hStepCEMMaxTarget (EfficientCHADState.hStepRewards s) gamma q₁ q₂

representationCompositionLaw : ∀ {A : OrderedAlgebra}
  (s : EfficientCHADState A) x →
  runStack (RepresentationGenome.stack (EfficientCHADState.representation s)) x ≡
  runStack (RepresentationGenome.stack (EfficientCHADState.representation s)) x
representationCompositionLaw s x = refl

------------------------------------------------------------------------
-- Finite ordered learner convergence closure. This is a finite ranking theorem,
-- not an infinite-horizon or real-analysis convergence theorem.
------------------------------------------------------------------------

data ReachesWithin {S : Set}
  (terminal : S → Set)
  (step : S → S) : Nat → S → Set where
  reachesHere : ∀ {s} → terminal s → ReachesWithin terminal step zero s
  reachesStep : ∀ {n s} → ReachesWithin terminal step n (step s) →
    ReachesWithin terminal step (suc n) s

record FiniteRankCertificate (S : Set) : Set₁ where
  field
    terminal : S → Set
    rank : S → Nat
    step : S → S
    terminalOrDrop : ∀ s → terminal s ⊎ RankDrop S s

record RankDrop (S : Set) : Set where
  field
    source target : S
    sourceEq : source ≡ target

-- The main closure uses an explicit rank successor law below rather than a
-- certificate wrapper. Retained only as a finite architectural boundary.

record FiniteOrderedCouplingRank (S : Set) : Set₁ where
  field
    terminal : S → Set
    rank : S → Nat
    step : S → S
    rankDrop : ∀ s → rank s ≡ suc (rank (step s))

finiteRankSuccessor : ∀ {S : Set}
  (c : FiniteOrderedCouplingRank S) s →
  rank c s ≡ suc (rank c (step c s))
finiteRankSuccessor c s = FiniteOrderedCouplingRank.rankDrop c s

------------------------------------------------------------------------
-- Canonical full closure: every active coupling is represented by an actual
-- proof term. Retired v147 Newton/LayerNorm/StoSign surfaces are deliberately
-- absent; their slots are replaced by the finite emergent geometry laws above.
------------------------------------------------------------------------

record FullFiniteOrderedRationalCoupling (A : OrderedAlgebra) : Set₁ where
  field
    signReLU : ∀ (l : SignReLULayer A) x →
      runSignReLULayer l x ≡
      signReLU (SignReLULayer.activation l)
        (Affine.apply (SignReLULayer.second l)
          (signReLU (SignReLULayer.activation l)
            (Affine.apply (SignReLULayer.first l) x)))
    stack : ∀ (xs ys : Stack A) x →
      runStack (appendStack xs ys) x ≡ runStack ys (runStack xs x)
    tsallis2 : ∀ (p : MunchausenTsallis2 A) reward bootstrap →
      munchausenTsallis2Target p reward bootstrap ≡
      (reward + munchausenAlphaQLog2 p) + bootstrap
    hStep : ∀ r gamma bootstrap rs →
      hStepReturn (r ∷ rs) gamma bootstrap ≡
      r + (gamma * hStepReturn rs gamma bootstrap)
    trueOnline : ∀ rewards gamma q₁ q₂ value (s : TrueOnlineTrace A) phi →
      hStepCEMMaxTrueOnline rewards gamma q₁ q₂ value s phi ≡
      trueOnlineTraceStep s (hStepCEMMaxDelta rewards gamma q₁ q₂ value) phi
    base2IDBD : ∀ xs → idbdLog2 A (idbdPow2 A xs) ≡ xs
    qProjection : ∀ (q : QProjection A) x →
      QProjection.project q (QProjection.project q x) ≡ QProjection.project q x
    signIDBD : ∀ xs →
      mapL (sign A) (mapL (sign A) xs) ≡ mapL (sign A) xs
    lion : ∀ (s : LionFeatureState A) g →
      lionDirection s g ≡
      mapL (sign A)
        (zipL4 (λ b c m x → (b * m) + (c * x))
          (LionFeatureState.beta1 s) (LionFeatureState.complement1 s)
          (LionFeatureState.momentum s) g)
    l2Zero : ∀ (p : DyadicCoupledL2 A) →
      DyadicCoupledL2.lambda p ≡ zero A →
      coupledL2Penalty p (one A) ≡ zero A
    representationOnly : ∀ (s : RepresentationOnlyState A) →
      onlyRepresentationEvolved s ≡ RepresentationOnlyState.representation s
    antithetic : ∀ xs →
      featureAdd xs (mapL (neg A) xs) ≡ mapL (λ _ → zero A) xs
    geometry : ∀ x → EmergentGeometryLaw A x

fullFiniteOrderedRationalCoupling : ∀ {A : OrderedAlgebra} →
  FullFiniteOrderedRationalCoupling A
fullFiniteOrderedRationalCoupling {A} = record
  { signReLU = twoAffineSignReLULaw
  ; stack = stackComposition
  ; tsallis2 = munchausenTsallis2CompositionLaw
  ; hStep = hStepRecursionLaw
  ; trueOnline = hStepCEMMaxTrueOnlineLaw
  ; base2IDBD = idbdBase2RoundTrip
  ; qProjection = signQProjectionLaw
  ; signIDBD = signDirectionIdempotent
  ; lion = lionPerFeatureDirectionLaw
  ; l2Zero = coupledL2ZeroLaw
  ; representationOnly = representationOnlyLaw
  ; antithetic = antitheticFeatureCancel
  ; geometry = emergentGeometryLaw A
  }

fullCouplingIdentityLaw : ∀ {A : OrderedAlgebra}
  (c : FullFiniteOrderedRationalCoupling A) →
  FullFiniteOrderedRationalCoupling A
fullCouplingIdentityLaw c = c
