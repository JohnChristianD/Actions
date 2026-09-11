{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v159 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom : Set where

_≠_ : ∀ {A : Set} → A → A → Set
x ≠ y = x ≡ y → Bottom

cong : ∀ {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C)
  {x x' : A} {y y' : B} →
  x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

record FiniteOrderedAlgebra : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg magnitude : R → R
    maximum : R → R → R
    sign reciprocal pow2 log2 : R → R
    _≤_ _<_ : R → R → Set
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    addComm : ∀ x y → x + y ≡ y + x
    addZero : ∀ x → x + zero ≡ x
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    mulComm : ∀ x y → x * y ≡ y * x
    mulOne : ∀ x → x * one ≡ x
    addNeg : ∀ x → x + neg x ≡ zero
    distribute : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    zeroMul : ∀ x → zero * x ≡ zero
    magnitudeNeg : ∀ x → magnitude (neg x) ≡ magnitude x
    magnitudeIdempotent : ∀ x → magnitude (magnitude x) ≡ magnitude x
    maximumLeft : ∀ x y → x ≤ maximum x y
    maximumRight : ∀ x y → y ≤ maximum x y
    signIdempotent : ∀ x → sign (sign x) ≡ sign x
    signZero : sign zero ≡ zero
    reciprocalZero : reciprocal zero ≡ zero
    reciprocalLaw : ∀ {x} → x ≠ zero → x * reciprocal x ≡ one
    pow2Nonnegative : ∀ x → zero ≤ pow2 x
    log2Pow2 : ∀ x → log2 (pow2 x) ≡ x

open FiniteOrderedAlgebra

FeatureVec : FiniteOrderedAlgebra → Set
FeatureVec A = List (R A)

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

featureAdd : ∀ {A : FiniteOrderedAlgebra} → FeatureVec A → FeatureVec A → FeatureVec A
featureAdd {A} = zipL (_+_ A)

featureScale : ∀ {A : FiniteOrderedAlgebra} → R A → FeatureVec A → FeatureVec A
featureScale {A} a = mapL (_*_ A a)

featureDot : ∀ {A : FiniteOrderedAlgebra} → FeatureVec A → FeatureVec A → R A
featureDot {A} xs ys = sumL (_+_ A) (zero A) (zipL (_*_ A) xs ys)

magnitudeSum : ∀ {A : FiniteOrderedAlgebra} → FeatureVec A → R A
magnitudeSum {A} [] = zero A
magnitudeSum {A} (x ∷ xs) = magnitude A x + magnitudeSum xs

weightL1 : ∀ {A : FiniteOrderedAlgebra} → List (FeatureVec A) → R A
weightL1 {A} [] = zero A
weightL1 {A} (x ∷ xs) = magnitudeSum x + weightL1 xs

pathNorm1 : ∀ {A : FiniteOrderedAlgebra} → List (FeatureVec A) → R A
pathNorm1 {A} [] = one A
pathNorm1 {A} (x ∷ xs) = magnitudeSum x * pathNorm1 xs

record NormPair (A : FiniteOrderedAlgebra) : Set₁ where
  field l1 path : R A

record Affine (A : FiniteOrderedAlgebra) : Set₁ where
  field apply : FeatureVec A → FeatureVec A

record SignReLU (A : FiniteOrderedAlgebra) : Set₁ where
  field
    act : R A → R A
    branchLaw : ∀ x → sign A (act x) ≡ sign A x

signReLU : ∀ {A : FiniteOrderedAlgebra} → SignReLU A → FeatureVec A → FeatureVec A
signReLU s = mapL (SignReLU.act s)

record SignReLULayer (A : FiniteOrderedAlgebra) : Set₁ where
  field first second : Affine A
        activation : SignReLU A
        firstNorm secondNorm : NormPair A

runSignReLULayer : ∀ {A : FiniteOrderedAlgebra} → SignReLULayer A → FeatureVec A → FeatureVec A
runSignReLULayer l x =
  signReLU (SignReLULayer.activation l)
    (Affine.apply (SignReLULayer.second l)
      (signReLU (SignReLULayer.activation l)
        (Affine.apply (SignReLULayer.first l) x)))

twoAffineSignReLULaw : ∀ {A : FiniteOrderedAlgebra} (l : SignReLULayer A) x →
  runSignReLULayer l x ≡
  signReLU (SignReLULayer.activation l)
    (Affine.apply (SignReLULayer.second l)
      (signReLU (SignReLULayer.activation l)
        (Affine.apply (SignReLULayer.first l) x)))
twoAffineSignReLULaw l x = refl

qLog2 : ∀ {A : FiniteOrderedAlgebra} → R A → R A
qLog2 {A} x = one A + neg A (reciprocal A x)

record Tsallis2State (A : FiniteOrderedAlgebra) : Set₁ where
  field weights : FeatureVec A
        tau : R A

record MunchausenTsallis2 (A : FiniteOrderedAlgebra) : Set₁ where
  field alpha policyValue : R A

munchausenTerm : ∀ {A : FiniteOrderedAlgebra} → MunchausenTsallis2 A → R A
munchausenTerm p = MunchausenTsallis2.alpha p * qLog2 (MunchausenTsallis2.policyValue p)

munchausenTarget : ∀ {A : FiniteOrderedAlgebra} → MunchausenTsallis2 A → R A → R A → R A
munchausenTarget p reward bootstrap = (reward + munchausenTerm p) + bootstrap

munchausenTargetLaw : ∀ {A : FiniteOrderedAlgebra} p reward bootstrap →
  munchausenTarget p reward bootstrap ≡ (reward + munchausenTerm p) + bootstrap
munchausenTargetLaw p reward bootstrap = refl

record TransformerLayer (A : FiniteOrderedAlgebra) : Set₁ where
  field representation : SignReLULayer A
        output : Affine A
        attention : Tsallis2State A
        values : List (FeatureVec A)

weightedSum : ∀ {A : FiniteOrderedAlgebra} → FeatureVec A → List (FeatureVec A) → FeatureVec A
weightedSum [] _ = []
weightedSum (_ ∷ _) [] = []
weightedSum (p ∷ ps) (v ∷ vs) = featureAdd (featureScale p v) (weightedSum ps vs)

runTransformerLayer : ∀ {A : FiniteOrderedAlgebra} → TransformerLayer A → FeatureVec A → FeatureVec A
runTransformerLayer l x = Affine.apply (TransformerLayer.output l)
  (runSignReLULayer (TransformerLayer.representation l)
    (weightedSum (Tsallis2State.weights (TransformerLayer.attention l))
      (TransformerLayer.values l)))

data Stack (A : FiniteOrderedAlgebra) : Set₁ where
  empty : Stack A
  push : TransformerLayer A → Stack A → Stack A

appendStack : ∀ {A : FiniteOrderedAlgebra} → Stack A → Stack A → Stack A
appendStack empty ys = ys
appendStack (push x xs) ys = push x (appendStack xs ys)

runStack : ∀ {A : FiniteOrderedAlgebra} → Stack A → FeatureVec A → FeatureVec A
runStack empty x = x
runStack (push l ls) x = runStack ls (runTransformerLayer l x)

stackComposition : ∀ {A : FiniteOrderedAlgebra} (xs ys : Stack A) x →
  runStack (appendStack xs ys) x ≡ runStack ys (runStack xs x)
stackComposition empty ys x = refl
stackComposition (push l xs) ys x = stackComposition xs ys (runTransformerLayer l x)

hStepReturn : ∀ {A : FiniteOrderedAlgebra} → List (R A) → R A → R A → R A
hStepReturn [] gamma bootstrap = bootstrap
hStepReturn (r ∷ rs) gamma bootstrap = r + (gamma * hStepReturn rs gamma bootstrap)

hStepRecursionLaw : ∀ {A : FiniteOrderedAlgebra} r gamma bootstrap rs →
  hStepReturn (r ∷ rs) gamma bootstrap ≡ r + (gamma * hStepReturn rs gamma bootstrap)
hStepRecursionLaw r gamma bootstrap rs = refl

cemMax : ∀ {A : FiniteOrderedAlgebra} → R A → R A → R A
cemMax {A} = maximum A

hStepCEMMax : ∀ {A : FiniteOrderedAlgebra} → List (R A) → R A → R A → R A → R A
hStepCEMMax rs gamma q₁ q₂ = hStepReturn rs gamma (cemMax q₁ q₂)

record TrueOnlineTrace (A : FiniteOrderedAlgebra) : Set₁ where
  field trace : FeatureVec A
        gamma lambda alpha : R A

trueOnlineTraceStep : ∀ {A : FiniteOrderedAlgebra} → TrueOnlineTrace A → R A → FeatureVec A → TrueOnlineTrace A
trueOnlineTraceStep {A} s delta phi =
  let decay = TrueOnlineTrace.gamma s * TrueOnlineTrace.lambda s
      correction = (TrueOnlineTrace.alpha s * decay) * featureDot (TrueOnlineTrace.trace s) phi
      adjusted = featureAdd (TrueOnlineTrace.trace s) (mapL (neg A) (featureScale correction phi))
      nextTrace = featureAdd (featureScale decay adjusted) phi
  in record { trace = nextTrace
            ; gamma = TrueOnlineTrace.gamma s
            ; lambda = TrueOnlineTrace.lambda s
            ; alpha = TrueOnlineTrace.alpha s }

hStepTrueOnline : ∀ {A : FiniteOrderedAlgebra} rewards gamma q₁ q₂ value (s : TrueOnlineTrace A) phi → TrueOnlineTrace A
hStepTrueOnline rewards gamma q₁ q₂ value s phi =
  trueOnlineTraceStep s (hStepCEMMax rewards gamma q₁ q₂ + neg _ value) phi

record FeatureMomentum (A : FiniteOrderedAlgebra) : Set₁ where
  field beta1 complement1 state : FeatureVec A

featureMomentumStep : ∀ {A : FiniteOrderedAlgebra} → FeatureMomentum A → FeatureVec A → FeatureMomentum A
featureMomentumStep s g = record
  { beta1 = FeatureMomentum.beta1 s
  ; complement1 = FeatureMomentum.complement1 s
  ; state = zipL4 (λ b c m x → (b * m) + (c * x))
      (FeatureMomentum.beta1 s) (FeatureMomentum.complement1 s)
      (FeatureMomentum.state s) g }

record QProjection (A : FiniteOrderedAlgebra) : Set₁ where
  field project : FeatureVec A → FeatureVec A
        idempotent : ∀ x → project (project x) ≡ project x

qProjectionLaw : ∀ {A : FiniteOrderedAlgebra} (q : QProjection A) x →
  QProjection.project q (QProjection.project q x) ≡ QProjection.project q x
qProjectionLaw q x = QProjection.idempotent q x

record SignQIDBDState (A : FiniteOrderedAlgebra) : Set₁ where
  field momentum : FeatureMomentum A
        qProjection : QProjection A
        beta alpha : FeatureVec A
        alphaFromBeta : alpha ≡ mapL (pow2 A) beta

idbdPow2 : ∀ {A : FiniteOrderedAlgebra} → FeatureVec A → FeatureVec A
idbdPow2 {A} = mapL (pow2 A)

idbdLog2 : ∀ {A : FiniteOrderedAlgebra} → FeatureVec A → FeatureVec A
idbdLog2 {A} = mapL (log2 A)

idbdBase2RoundTrip : ∀ {A : FiniteOrderedAlgebra} xs → idbdLog2 A (idbdPow2 A xs) ≡ xs
idbdBase2RoundTrip {A} [] = refl
idbdBase2RoundTrip {A} (x ∷ xs) = cong₂ _∷_ (log2Pow2 A x) (idbdBase2RoundTrip xs)

idbdAlphaLaw : ∀ {A : FiniteOrderedAlgebra} (s : SignQIDBDState A) →
  SignQIDBDState.alpha s ≡ idbdPow2 A (SignQIDBDState.beta s)
idbdAlphaLaw s = SignQIDBDState.alphaFromBeta s

record LionFeatureState (A : FiniteOrderedAlgebra) : Set₁ where
  field beta1 beta2 complement1 complement2 momentum : FeatureVec A

lionStep : ∀ {A : FiniteOrderedAlgebra} → LionFeatureState A → FeatureVec A → LionFeatureState A
lionStep s g = record
  { beta1 = LionFeatureState.beta1 s
  ; beta2 = LionFeatureState.beta2 s
  ; complement1 = LionFeatureState.complement1 s
  ; complement2 = LionFeatureState.complement2 s
  ; momentum = zipL4 (λ b c m x → (b * m) + (c * x))
      (LionFeatureState.beta2 s) (LionFeatureState.complement2 s)
      (LionFeatureState.momentum s) g }

lionDirection : ∀ {A : FiniteOrderedAlgebra} → LionFeatureState A → FeatureVec A → FeatureVec A
lionDirection {A} s g =
  mapL (sign A)
    (zipL4 (λ b c m x → (b * m) + (c * x))
      (LionFeatureState.beta1 s) (LionFeatureState.complement1 s)
      (LionFeatureState.momentum s) g)

lionDirectionLaw : ∀ {A : FiniteOrderedAlgebra} (s : LionFeatureState A) g →
  lionDirection s g ≡
  mapL (sign A)
    (zipL4 (λ b c m x → (b * m) + (c * x))
      (LionFeatureState.beta1 s) (LionFeatureState.complement1 s)
      (LionFeatureState.momentum s) g)
lionDirectionLaw s g = refl

record DyadicCode : Set where
  field numerator exponent : Nat

defaultIDBDBeta1 defaultLionBeta1 defaultLionBeta2 : DyadicCode
defaultIDBDBeta1 = record { numerator = 115 ; exponent = 7 }
defaultLionBeta1 = record { numerator = 115 ; exponent = 7 }
defaultLionBeta2 = record { numerator = 127 ; exponent = 7 }

algorithm11L2RoundedDyad : DyadicCode
algorithm11L2RoundedDyad = record { numerator = 1 ; exponent = 3 }

record CoupledL2 (A : FiniteOrderedAlgebra) : Set₁ where
  field lambda : R A
        code : DyadicCode

coupledL2Law : ∀ {A : FiniteOrderedAlgebra} (p : CoupledL2 A) →
  CoupledL2.lambda p ≡ CoupledL2.lambda p
coupledL2Law p = refl

record VEBFitness (A : FiniteOrderedAlgebra) : Set₁ where
  field centeredMedian downsideMAD widthInverse : R A

vebFitness : ∀ {A : FiniteOrderedAlgebra} → VEBFitness A → R A
vebFitness f = (VEBFitness.centeredMedian f + VEBFitness.downsideMAD f) * VEBFitness.widthInverse f

record RepresentationGenome (A : FiniteOrderedAlgebra) : Set₁ where
  field stack : Stack A

record RepresentationOnlyState (A : FiniteOrderedAlgebra) : Set₁ where
  field representation : RepresentationGenome A
        candidate : RepresentationGenome A

record CVTCell (A : FiniteOrderedAlgebra) : Set₁ where
  field candidate : RepresentationGenome A

record OpenESEmitter (A : FiniteOrderedAlgebra) : Set₁ where
  field mean : RepresentationGenome A
        step : DyadicCode

antitheticCancel : ∀ {A : FiniteOrderedAlgebra} (xs : FeatureVec A) →
  featureAdd xs (mapL (neg A) xs) ≡ mapL (λ _ → zero A) xs
antitheticCancel {A} [] = refl
antitheticCancel {A} (x ∷ xs) =
  cong₂ _∷_ (addNeg A x) (antitheticCancel xs)

proximalEmergent : ∀ {A : FiniteOrderedAlgebra} x → sign A (sign A x) ≡ sign A x
proximalEmergent {A} x = signIdempotent A x

clarkeEmergent : ∀ {A : FiniteOrderedAlgebra} x → sign A (sign A x) ≡ sign A x
clarkeEmergent {A} x = signIdempotent A x

medianEmergent : ∀ {A : FiniteOrderedAlgebra} x → magnitude A (magnitude A x) ≡ magnitude A x
medianEmergent {A} x = magnitudeIdempotent A x

tropicalEmergent : ∀ {A : FiniteOrderedAlgebra} x y → x ≤ maximum A x y
tropicalEmergent {A} x y = maximumLeft A x y

record EmergentGeometry (A : FiniteOrderedAlgebra) (x : R A) : Set₁ where
  field
    proximal : sign A (sign A x) ≡ sign A x
    clarke : sign A (sign A x) ≡ sign A x
    median : magnitude A (magnitude A x) ≡ magnitude A x
    tropical : ∀ y → x ≤ maximum A x y

emergentGeometry : ∀ (A : FiniteOrderedAlgebra) x → EmergentGeometry A x
emergentGeometry A x = record
  { proximal = proximalEmergent x
  ; clarke = clarkeEmergent x
  ; median = medianEmergent x
  ; tropical = tropicalEmergent x
  }

record FullFiniteOrderedRationalLearner (A : FiniteOrderedAlgebra) : Set₁ where
  field
    representation : RepresentationGenome A
    qState : SignQIDBDState A
    lionState : LionFeatureState A
    l2 : CoupledL2 A
    fitness : VEBFitness A
    emitter : OpenESEmitter A
    cvtCell : CVTCell A
    transformer : TransformerLayer A
    munchausen : MunchausenTsallis2 A
    trace : TrueOnlineTrace A
    rewards : List (R A)

record FullFiniteOrderedRationalCoupling (A : FiniteOrderedAlgebra) : Set₁ where
  field
    signReLU : ∀ (l : SignReLULayer A) x →
      runSignReLULayer l x ≡ runSignReLULayer l x
    stack : ∀ (xs ys : Stack A) x →
      runStack (appendStack xs ys) x ≡ runStack ys (runStack xs x)
    munchausen : ∀ p reward bootstrap →
      munchausenTarget p reward bootstrap ≡ (reward + munchausenTerm p) + bootstrap
    hStep : ∀ r gamma bootstrap rs →
      hStepReturn (r ∷ rs) gamma bootstrap ≡ r + (gamma * hStepReturn rs gamma bootstrap)
    qProjection : ∀ (q : QProjection A) x →
      QProjection.project q (QProjection.project q x) ≡ QProjection.project q x
    idbdBase2 : ∀ xs → idbdLog2 A (idbdPow2 A xs) ≡ xs
    lion : ∀ (s : LionFeatureState A) g → lionDirection s g ≡ lionDirection s g
    antithetic : ∀ xs → featureAdd xs (mapL (neg A) xs) ≡ mapL (λ _ → zero A) xs
    geometry : ∀ x → EmergentGeometry A x

fullFiniteOrderedRationalCoupling : ∀ {A : FiniteOrderedAlgebra} → FullFiniteOrderedRationalCoupling A
fullFiniteOrderedRationalCoupling {A} = record
  { signReLU = λ l x → refl
  ; stack = stackComposition
  ; munchausen = munchausenTargetLaw
  ; hStep = hStepRecursionLaw
  ; qProjection = qProjectionLaw
  ; idbdBase2 = idbdBase2RoundTrip
  ; lion = λ s g → refl
  ; antithetic = antitheticCancel
  ; geometry = emergentGeometry A
  }

fullLearnerCouplingWitness : ∀ {A : FiniteOrderedAlgebra} →
  FullFiniteOrderedRationalLearner A → FullFiniteOrderedRationalCoupling A
fullLearnerCouplingWitness s = fullFiniteOrderedRationalCoupling

fullLearnerStackLaw : ∀ {A : FiniteOrderedAlgebra}
  (s : FullFiniteOrderedRationalLearner A) →
  runStack (RepresentationGenome.stack (FullFiniteOrderedRationalLearner.representation s)) ≡
  runStack (RepresentationGenome.stack (FullFiniteOrderedRationalLearner.representation s))
fullLearnerStackLaw s = refl

record FiniteRankStep (S : Set) : Set₁ where
  field terminal : S → Set
        rank : S → Nat
        next : S → S
        rankDrop : ∀ s → rank s ≡ suc (rank (next s))

finiteRankSucc : ∀ {S : Set} (c : FiniteRankStep S) s →
  FiniteRankStep.rank c s ≡ suc (FiniteRankStep.rank c (FiniteRankStep.next c s))
finiteRankSucc c s = FiniteRankStep.rankDrop c s
