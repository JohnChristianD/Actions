{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v156 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

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
zipL4 f (a ∷ as) (b ∷ bs) (c ∷ cs) (d ∷ ds) =
  f a b c d ∷ zipL4 f as bs cs ds

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

record Affine (A : OrderedAlgebra) : Set₁ where
  field apply : FeatureVec A → FeatureVec A

record SignReLU (A : OrderedAlgebra) : Set₁ where
  field act : R A → R A
        branchSign : ∀ x → sign A (act x) ≡ sign A x

signReLU : ∀ {A : OrderedAlgebra} → SignReLU A → FeatureVec A → FeatureVec A
signReLU s = mapL (SignReLU.act s)

signReLUFeaturewise : ∀ {A : OrderedAlgebra} (s : SignReLU A) (x : FeatureVec A) →
  signReLU s x ≡ signReLU s x
signReLUFeaturewise s x = refl

record NormPair (A : OrderedAlgebra) : Set₁ where
  field l1 path : R A

record SignReLULayer (A : OrderedAlgebra) : Set₁ where
  field first second : Affine A
        activation : SignReLU A
        firstNorm secondNorm : NormPair A

runSignReLULayer : ∀ {A : OrderedAlgebra} → SignReLULayer A → FeatureVec A → FeatureVec A
runSignReLULayer l x =
  signReLU (SignReLULayer.activation l)
    (Affine.apply (SignReLULayer.second l)
      (signReLU (SignReLULayer.activation l)
        (Affine.apply (SignReLULayer.first l) x)))

record Tsallis2State (A : OrderedAlgebra) : Set₁ where
  field scores weights : FeatureVec A
        tau : R A
        mass : featureDot weights (mapL (λ _ → one A) scores) ≡ one A

record TransformerLayer (A : OrderedAlgebra) : Set₁ where
  field representation : SignReLULayer A
        query key value output : Affine A
        queryNorm keyNorm valueNorm outputNorm : NormPair A
        attention : Tsallis2State A
        values : List (FeatureVec A)

weightedSum : ∀ {A : OrderedAlgebra} → FeatureVec A → List (FeatureVec A) → FeatureVec A
weightedSum [] _ = []
weightedSum (_ ∷ _) [] = []
weightedSum (p ∷ ps) (v ∷ vs) = featureAdd (featureScale p v) (weightedSum ps vs)

runTransformerLayer : ∀ {A : OrderedAlgebra} → TransformerLayer A → FeatureVec A → FeatureVec A
runTransformerLayer l x =
  Affine.apply (TransformerLayer.output l)
    (runSignReLULayer (TransformerLayer.representation l)
      (weightedSum
        (Tsallis2State.weights (TransformerLayer.attention l))
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

topTsallis2Utility : ∀ {A : OrderedAlgebra} → Tsallis2State A → R A
topTsallis2Utility s = featureDot (Tsallis2State.weights s) (Tsallis2State.scores s)

munchausenTsallis2Bonus : ∀ {A : OrderedAlgebra} → Tsallis2State A → R A
munchausenTsallis2Bonus s =
  one A + neg A (featureDot (Tsallis2State.weights s) (Tsallis2State.weights s))

munchausenTsallis2Target : ∀ {A : OrderedAlgebra} →
  Tsallis2State A → R A → R A → R A
munchausenTsallis2Target s reward bootstrap =
  reward + munchausenTsallis2Bonus s + bootstrap

hStepReturn : ∀ {A : OrderedAlgebra} → List (R A) → R A → R A → R A
hStepReturn {A} [] gamma bootstrap = bootstrap
hStepReturn {A} (r ∷ rs) gamma bootstrap =
  r + gamma * hStepReturn rs gamma bootstrap

hStepOne : ∀ {A : OrderedAlgebra} (r gamma bootstrap : R A) →
  hStepReturn (r ∷ []) gamma bootstrap ≡ r + gamma * bootstrap
hStepOne r gamma bootstrap = refl

cemMax : ∀ {A : OrderedAlgebra} → R A → R A → R A
cemMax {A} = max A

hStepCEMMaxTarget : ∀ {A : OrderedAlgebra} →
  List (R A) → R A → R A → R A → R A
hStepCEMMaxTarget rewards gamma q₁ q₂ =
  hStepReturn rewards gamma (cemMax q₁ q₂)

record TrueOnlineTrace (A : OrderedAlgebra) : Set₁ where
  field trace : FeatureVec A
        previousDelta gamma lambda alpha : R A

trueOnlineTraceStep : ∀ {A : OrderedAlgebra} →
  TrueOnlineTrace A → R A → FeatureVec A → TrueOnlineTrace A
trueOnlineTraceStep s delta phi =
  let decay = TrueOnlineTrace.gamma s * TrueOnlineTrace.lambda s
      correction = TrueOnlineTrace.alpha s * decay *
        featureDot (TrueOnlineTrace.trace s) phi
      adjusted = featureAdd
        (TrueOnlineTrace.trace s)
        (mapL (neg A) (featureScale correction phi))
      nextTrace = featureAdd (featureScale decay adjusted) phi
  in record
    { trace = nextTrace
    ; previousDelta = delta
    ; gamma = TrueOnlineTrace.gamma s
    ; lambda = TrueOnlineTrace.lambda s
    ; alpha = TrueOnlineTrace.alpha s
    }

hStepCEMMaxDelta : ∀ {A : OrderedAlgebra} →
  List (R A) → R A → R A → R A → R A → R A
hStepCEMMaxDelta rewards gamma q₁ q₂ value =
  hStepCEMMaxTarget rewards gamma q₁ q₂ + neg _ value

hStepCEMMaxTrueOnline : ∀ {A : OrderedAlgebra}
  (rewards : List (R A)) gamma q₁ q₂ value
  (s : TrueOnlineTrace A) phi → TrueOnlineTrace A
hStepCEMMaxTrueOnline rewards gamma q₁ q₂ value s phi =
  trueOnlineTraceStep s (hStepCEMMaxDelta rewards gamma q₁ q₂ value) phi

hStepCEMMaxTraceDelta : ∀ {A : OrderedAlgebra}
  (rewards : List (R A)) gamma q₁ q₂ value
  (s : TrueOnlineTrace A) phi →
  TrueOnlineTrace.previousDelta
    (hStepCEMMaxTrueOnline rewards gamma q₁ q₂ value s phi) ≡
  hStepCEMMaxDelta rewards gamma q₁ q₂ value
hStepCEMMaxTraceDelta rewards gamma q₁ q₂ value s phi = refl

record FeatureMomentum (A : OrderedAlgebra) : Set₁ where
  field beta1 complement1 state : FeatureVec A

featureMomentumStep : ∀ {A : OrderedAlgebra} →
  FeatureMomentum A → FeatureVec A → FeatureMomentum A
featureMomentumStep s g = record
  { beta1 = FeatureMomentum.beta1 s
  ; complement1 = FeatureMomentum.complement1 s
  ; state = zipL4 (λ b c m x → b * m + c * x)
      (FeatureMomentum.beta1 s)
      (FeatureMomentum.complement1 s)
      (FeatureMomentum.state s) g
  }

record QProjection (A : OrderedAlgebra) : Set₁ where
  field project : FeatureVec A → FeatureVec A
        idempotent : ∀ x → project (project x) ≡ project x

record SignQIDBDState (A : OrderedAlgebra) : Set₁ where
  field momentum : FeatureMomentum A
        qProjection : QProjection A

signQIDBDDirection : ∀ {A : OrderedAlgebra} → SignQIDBDState A → FeatureVec A
signQIDBDDirection s =
  mapL (sign A)
    (QProjection.project (SignQIDBDState.qProjection s)
      (FeatureMomentum.state (SignQIDBDState.momentum s)))

signQIDBDSignIdempotent : ∀ {A : OrderedAlgebra} x →
  sign A (sign A x) ≡ sign A x
signQIDBDSignIdempotent {A} x = signIdempotent A x

record LionFeatureState (A : OrderedAlgebra) : Set₁ where
  field beta1 beta2 complement1 complement2 momentum : FeatureVec A

lionDirection : ∀ {A : OrderedAlgebra} → LionFeatureState A →
  FeatureVec A → FeatureVec A
lionDirection s g = mapL (sign A)
  (zipL4 (λ b c m x → b * m + c * x)
    (LionFeatureState.beta1 s)
    (LionFeatureState.complement1 s)
    (LionFeatureState.momentum s) g)

lionMomentumStep : ∀ {A : OrderedAlgebra} → LionFeatureState A →
  FeatureVec A → LionFeatureState A
lionMomentumStep s g = record
  { beta1 = LionFeatureState.beta1 s
  ; beta2 = LionFeatureState.beta2 s
  ; complement1 = LionFeatureState.complement1 s
  ; complement2 = LionFeatureState.complement2 s
  ; momentum = zipL4 (λ b c m x → b * m + c * x)
      (LionFeatureState.beta2 s)
      (LionFeatureState.complement2 s)
      (LionFeatureState.momentum s) g
  }

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
  (VEBFitness.centeredMedian f + VEBFitness.downsideMAD f) *
  VEBFitness.widthInverse f

record RepresentationGenome (A : OrderedAlgebra) : Set₁ where
  field stack : Stack A

record RepresentationCandidate (A : OrderedAlgebra) : Set₁ where
  field representation : RepresentationGenome A
        fitness : VEBFitness A

representationOnlyLaw : ∀ {A : OrderedAlgebra}
  (c : RepresentationCandidate A) →
  RepresentationCandidate.representation c ≡ RepresentationCandidate.representation c
representationOnlyLaw c = refl

record CVTCell (A : OrderedAlgebra) : Set₁ where
  field candidate : RepresentationCandidate A

record OpenESEmitter (A : OrderedAlgebra) : Set₁ where
  field mean : RepresentationGenome A
        step : DyadicCode

antitheticCancel : ∀ {A : OrderedAlgebra} (x : R A) →
  x + neg A x ≡ zero A
antitheticCancel x = addNegR A x

record L1SubgradientChoice (A : OrderedAlgebra) (x s : R A) : Set where
  field
    nonzeroLaw : x ≠ zero A → s ≡ sign A x
    zeroLower : x ≡ zero A → zero A ≤ s
    zeroUpper : x ≡ zero A → s ≤ one A

record ProximalL1Geometry (A : OrderedAlgebra) : Set₁ where
  field prox : R A → R A → R A
        resolventLaw : ∀ x t → prox (prox x t) t ≡ prox x t

record ClarkeEnvelope (A : OrderedAlgebra) : Set₁ where
  field branchSlope : List (R A)
        envelope : R A → List (R A)

record MedianQuantileGeometry (A : OrderedAlgebra) : Set₁ where
  field median quantile : List (R A) → R A

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

record EfficientCHADState (A : OrderedAlgebra) : Set₁ where
  field representation : RepresentationGenome A
        qState : SignQIDBDState A
        lionState : LionFeatureState A
        trace : TrueOnlineTrace A
        fitness : VEBFitness A
        l2 : DyadicCoupledL2 A

onlyRepresentationEvolved : ∀ {A : OrderedAlgebra} →
  EfficientCHADState A → RepresentationGenome A
onlyRepresentationEvolved s = EfficientCHADState.representation s
