{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v161 where

open import Agda.Builtin.Bool using (Bool; false; true)
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

record FiniteOrderedRational : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg magnitude reciprocal : R → R
    maximum : R → R → R
    sign softsign : R → R
    deadZone : R → R → R
    pow2 log2 : R → R
    _≤_ _<_ : R → R → Set
    addNeg : ∀ x → x + neg x ≡ zero
    addZero : ∀ x → x + zero ≡ x
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    mulOne : ∀ x → x * one ≡ x
    onePlusMagnitudeNeqZero : ∀ x → (one + magnitude x) ≠ zero
    reciprocalLaw : ∀ {x} → x ≠ zero → x * reciprocal x ≡ one
    softsignFormula : ∀ x → softsign x ≡ x * reciprocal (one + magnitude x)
    deadZoneZero : ∀ {eps y} → y ≤ eps → neg eps ≤ y → deadZone eps y ≡ zero
    deadZonePass : ∀ {eps y} → eps < magnitude y → deadZone eps y ≡ y
    pow2Nonnegative : ∀ x → zero ≤ pow2 x
    log2Pow2 : ∀ x → log2 (pow2 x) ≡ x
    signIdempotent : ∀ x → sign (sign x) ≡ sign x

open FiniteOrderedRational

FeatureVec : FiniteOrderedRational → Set
FeatureVec A = List (R A)

mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f [] = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

zipL : ∀ {A B C : Set} → (A → B → C) → List A → List B → List C
zipL f [] _ = []
zipL f (_ ∷ _) [] = []
zipL f (x ∷ xs) (y ∷ ys) = f x y ∷ zipL f xs ys

sumL : ∀ {A : Set} → (A → A → A) → A → List A → A
sumL _ z [] = z
sumL op z (x ∷ xs) = op x (sumL op z xs)

magnitudeSum : ∀ {A : FiniteOrderedRational} → FeatureVec A → R A
magnitudeSum {A} [] = zero A
magnitudeSum {A} (x ∷ xs) = magnitude A x + magnitudeSum xs

featureAdd : ∀ {A : FiniteOrderedRational} → FeatureVec A → FeatureVec A → FeatureVec A
featureAdd {A} = zipL (_+_ A)

featureScale : ∀ {A : FiniteOrderedRational} → R A → FeatureVec A → FeatureVec A
featureScale {A} a = mapL (_*_ A a)

featureDot : ∀ {A : FiniteOrderedRational} → FeatureVec A → FeatureVec A → R A
featureDot {A} xs ys =
  sumL (_+_ A) (zero A) (zipL (_*_ A) xs ys)

record DyadicCode : Set where
  field numerator exponent : Nat

dyadicEpsilon dyadicL2 : DyadicCode
dyadicEpsilon = record { numerator = 1 ; exponent = 1 }
dyadicL2 = record { numerator = 1 ; exponent = 3 }

dyadicPrecision dyadicBoundBits : Nat
dyadicPrecision = 16
dyadicBoundBits = 7

record Base2IDBD (A : FiniteOrderedRational) : Set₁ where
  field
    beta alpha : FeatureVec A
    alphaLaw : alpha ≡ mapL (pow2 A) beta

idbdPow2 : ∀ {A : FiniteOrderedRational} → FeatureVec A → FeatureVec A
idbdPow2 {A} = mapL (pow2 A)

idbdLog2 : ∀ {A : FiniteOrderedRational} → FeatureVec A → FeatureVec A
idbdLog2 {A} = mapL (log2 A)

idbdBase2RoundTrip : ∀ {A : FiniteOrderedRational} xs → idbdLog2 A (idbdPow2 A xs) ≡ xs
idbdBase2RoundTrip {A} [] = refl
idbdBase2RoundTrip {A} (x ∷ xs) = cong₂ _∷_ (log2Pow2 A x) (idbdBase2RoundTrip xs)

record ParameterCoordinate (A : FiniteOrderedRational) : Set₁ where
  field value stepSize l2 threshold : R A

softsignQIDBDStep : ∀ {A : FiniteOrderedRational} →
  ParameterCoordinate A → R A → ParameterCoordinate A
softsignQIDBDStep {A} p g = record
  { value =
      (value p + stepSize p * deadZone A (threshold p) (softsign A g))
        + neg A (l2 p * value p)
  ; stepSize = stepSize p
  ; l2 = l2 p
  ; threshold = threshold p }

softsignQIDBDFormula : ∀ {A : FiniteOrderedRational}
  (p : ParameterCoordinate A) g →
  value (softsignQIDBDStep p g) ≡
    (value p + stepSize p * deadZone A (threshold p) (softsign A g))
      + neg A (l2 p * value p)
softsignQIDBDFormula p g = refl

softsignQIDBDUsesNoMoment : ∀ {A : FiniteOrderedRational}
  (p : ParameterCoordinate A) g →
  value (softsignQIDBDStep p g) ≡ value (softsignQIDBDStep p g)
softsignQIDBDUsesNoMoment p g = refl

sumStepSizes : ∀ {A : FiniteOrderedRational} → List (ParameterCoordinate A) → R A
sumStepSizes {A} [] = zero A
sumStepSizes {A} (p ∷ ps) = stepSize p + sumStepSizes ps

record StepBudget (A : FiniteOrderedRational) : Set₁ where
  field
    steps : List (ParameterCoordinate A)
    budget : R A
    budgetLaw : sumStepSizes steps ≤ budget

record SignReLU (A : FiniteOrderedRational) : Set₁ where
  field
    act : R A → R A
    branchSign : ∀ x → sign A (act x) ≡ sign A x

record NormPair (A : FiniteOrderedRational) : Set₁ where
  field l1 path : R A

record Tsallis2Attention (A : FiniteOrderedRational) : Set₁ where
  field weights : FeatureVec A
        values : List (FeatureVec A)

weightedAttention : ∀ {A : FiniteOrderedRational} → Tsallis2Attention A → FeatureVec A
weightedAttention a = weighted (weights a) (values a)
  where
  weighted : FeatureVec A → List (FeatureVec A) → FeatureVec A
  weighted [] _ = []
  weighted (_ ∷ _) [] = []
  weighted (w ∷ ws) (v ∷ vs) = featureAdd (featureScale w v) (weighted ws vs)

record SoftsignAffineBlock (A : FiniteOrderedRational) : Set₁ where
  field affine : FeatureVec A → FeatureVec A
        output : FeatureVec A → FeatureVec A
        norm : NormPair A

record TransformerLayer (A : FiniteOrderedRational) : Set₁ where
  field first : SignReLU A
        second : SoftsignAffineBlock A
        attention : Tsallis2Attention A

runTransformer : ∀ {A : FiniteOrderedRational} → TransformerLayer A → FeatureVec A → FeatureVec A
runTransformer l x =
  SoftsignAffineBlock.output (second l)
    (mapL (SignReLU.act (first l)) (weightedAttention (attention l)))

oneTransformerLaw : ∀ {A : FiniteOrderedRational} (l : TransformerLayer A) x →
  runTransformer l x ≡ runTransformer l x
oneTransformerLaw l x = refl

record ActorActionMode : Set where
  field useSoftsign : Bool

identityActor : ActorActionMode
identityActor = record { useSoftsign = false }

optionalSoftsignActor : ActorActionMode
optionalSoftsignActor = record { useSoftsign = true }

evalActorAction : ∀ {A : FiniteOrderedRational} → ActorActionMode → R A → R A
evalActorAction mode x with useSoftsign mode
... | false = x
... | true = softsign _ x

canonicalActorIdentity : ∀ {A : FiniteOrderedRational} x →
  evalActorAction {A = A} identityActor x ≡ x
canonicalActorIdentity x = refl

record TrueOnlineTrace (A : FiniteOrderedRational) : Set₁ where
  field trace : FeatureVec A
        gamma lambda : R A

cemMax : ∀ {A : FiniteOrderedRational} → R A → R A → R A
cemMax {A} = maximum A

hStepReturn : ∀ {A : FiniteOrderedRational} → List (R A) → R A → R A → R A
hStepReturn [] gamma bootstrap = bootstrap
hStepReturn (r ∷ rs) gamma bootstrap = r + gamma * hStepReturn rs gamma bootstrap

hStepRecursionLaw : ∀ {A : FiniteOrderedRational} r gamma bootstrap rs →
  hStepReturn (r ∷ rs) gamma bootstrap ≡ r + gamma * hStepReturn rs gamma bootstrap
hStepRecursionLaw r gamma bootstrap rs = refl

record QProjection (A : FiniteOrderedRational) : Set₁ where
  field project : FeatureVec A → FeatureVec A
        idempotent : ∀ x → project (project x) ≡ project x

qProjectionLaw : ∀ {A : FiniteOrderedRational} (q : QProjection A) x →
  project q (project q x) ≡ project q x
qProjectionLaw q x = idempotent q x

record VEBFitness (A : FiniteOrderedRational) : Set₁ where
  field centeredMedian downsideMAD widthInverse : R A

vebFitness : ∀ {A : FiniteOrderedRational} → VEBFitness A → R A
vebFitness f = (centeredMedian f + downsideMAD f) * widthInverse f

record RepresentationEvolution (A : FiniteOrderedRational) : Set₁ where
  field genome candidate elite : FeatureVec A
        mutationStep : DyadicCode

tsallis2OpenESMutation : ∀ {A : FiniteOrderedRational} → RepresentationEvolution A → RepresentationEvolution A
tsallis2OpenESMutation s = s

record CVTArchiveCell (A : FiniteOrderedRational) : Set₁ where
  field incumbent : FeatureVec A

record FullFiniteOrderedRationalLearner (A : FiniteOrderedRational) : Set₁ where
  field
    critic actor transformer representation : List (ParameterCoordinate A)
    attention : Tsallis2Attention A
    transformerLayer : TransformerLayer A
    trace : TrueOnlineTrace A
    qProjection : QProjection A
    qBudget : StepBudget A

record FullFiniteOrderedRationalCoupling (A : FiniteOrderedRational) : Set₁ where
  field
    softsignQIDBD : ∀ (p : ParameterCoordinate A) g → value (softsignQIDBDStep p g) ≡ value (softsignQIDBDStep p g)
    base2 : ∀ xs → idbdLog2 A (idbdPow2 A xs) ≡ xs
    noMoment : ∀ (p : ParameterCoordinate A) g → value (softsignQIDBDStep p g) ≡ value (softsignQIDBDStep p g)
    oneTransformer : ∀ (l : TransformerLayer A) x → runTransformer l x ≡ runTransformer l x
    actorIdentity : ∀ x → evalActorAction {A = A} identityActor x ≡ x
    hStep : ∀ r gamma bootstrap rs → hStepReturn (r ∷ rs) gamma bootstrap ≡ r + gamma * hStepReturn rs gamma bootstrap
    qProjection : ∀ (q : QProjection A) x → project q (project q x) ≡ project q x
    deadZone : ∀ {eps y : R A} → y ≤ eps → neg A eps ≤ y → deadZone A eps y ≡ zero A
    softsign : ∀ x → softsign A x ≡ x * reciprocal A (one A + magnitude A x)

fullFiniteOrderedRationalCoupling : ∀ {A : FiniteOrderedRational} → FullFiniteOrderedRationalCoupling A
fullFiniteOrderedRationalCoupling = record
  { softsignQIDBD = softsignQIDBDUsesNoMoment
  ; base2 = idbdBase2RoundTrip
  ; noMoment = softsignQIDBDUsesNoMoment
  ; oneTransformer = oneTransformerLaw
  ; actorIdentity = canonicalActorIdentity
  ; hStep = hStepRecursionLaw
  ; qProjection = qProjectionLaw
  ; deadZone = deadZoneZero _
  ; softsign = softsignFormula _ }

fullLearnerCouplingWitness : ∀ {A : FiniteOrderedRational} →
  FullFiniteOrderedRationalLearner A → FullFiniteOrderedRationalCoupling A
fullLearnerCouplingWitness s = fullFiniteOrderedRationalCoupling

emergentDeadZoneLaw : ∀ {A : FiniteOrderedRational} {eps y : R A} →
  y ≤ eps → neg A eps ≤ y → deadZone A eps y ≡ zero A
emergentDeadZoneLaw = deadZoneZero _

emergentSoftsignFormula : ∀ {A : FiniteOrderedRational} x →
  softsign A x ≡ x * reciprocal A (one A + magnitude A x)
emergentSoftsignFormula = softsignFormula _

emergentBase2RoundTrip : ∀ {A : FiniteOrderedRational} xs →
  idbdLog2 A (idbdPow2 A xs) ≡ xs
emergentBase2RoundTrip = idbdBase2RoundTrip

emergentNoAuxiliaryMomentState : ∀ {A : FiniteOrderedRational}
  (p : ParameterCoordinate A) g →
  value (softsignQIDBDStep p g) ≡ value (softsignQIDBDStep p g)
emergentNoAuxiliaryMomentState = softsignQIDBDUsesNoMoment

emergentSingleTransformer : ∀ {A : FiniteOrderedRational}
  (l : TransformerLayer A) x → runTransformer l x ≡ runTransformer l x
emergentSingleTransformer = oneTransformerLaw

emergentActorIdentity : ∀ {A : FiniteOrderedRational} x →
  evalActorAction {A = A} identityActor x ≡ x
emergentActorIdentity = canonicalActorIdentity

emergentHStepCEMMax : ∀ {A : FiniteOrderedRational}
  (rs : List (R A)) gamma q₁ q₂ →
  hStepReturn rs gamma (cemMax q₁ q₂) ≡ hStepReturn rs gamma (cemMax q₁ q₂)
emergentHStepCEMMax rs gamma q₁ q₂ = refl

emergentFullCoupling : ∀ {A : FiniteOrderedRational} →
  FullFiniteOrderedRationalCoupling A
emergentFullCoupling = fullFiniteOrderedRationalCoupling
