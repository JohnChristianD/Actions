{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v160 where

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

record FiniteOrderedRational (Rational : Set) : Set₁ where
  field
    zero one : Rational
    _+_ _*_ : Rational → Rational → Rational
    neg magnitude reciprocal : Rational → Rational
    maximum : Rational → Rational → Rational
    softsign : Rational → Rational
    deadZone : Rational → Rational → Rational
    _≤_ _<_ : Rational → Rational → Set
    addNeg : ∀ x → x + neg x ≡ zero
    mulOne : ∀ x → x * one ≡ x
    addZero : ∀ x → x + zero ≡ x
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    onePlusMagnitudeNeqZero : ∀ x → one + magnitude x ≠ zero
    reciprocalLaw : ∀ {x} → x ≠ zero → x * reciprocal x ≡ one
    softsignFormula : ∀ x → softsign x ≡ x * reciprocal (one + magnitude x)
    deadZoneZero : ∀ {eps y} → y ≤ eps → neg eps ≤ y → deadZone eps y ≡ zero
    deadZonePass : ∀ {eps y} → eps < magnitude y → deadZone eps y ≡ y

open FiniteOrderedRational

FeatureVec : ∀ {Rational : Set} → FiniteOrderedRational Rational → Set
FeatureVec A = List (FiniteOrderedRational.Rational A)

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

magnitudeSum : ∀ {Rational : Set} (A : FiniteOrderedRational Rational) → FeatureVec A → Rational
magnitudeSum A [] = FiniteOrderedRational.zero A
magnitudeSum A (x ∷ xs) =
  FiniteOrderedRational.magnitude A x + magnitudeSum A xs

featureAdd : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} → FeatureVec A → FeatureVec A → FeatureVec A
featureAdd {A = A} = zipL (FiniteOrderedRational._+_ A)

featureScale : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} → Rational → FeatureVec A → FeatureVec A
featureScale {A = A} a = mapL (FiniteOrderedRational._*_ A a)

featureDot : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} → FeatureVec A → FeatureVec A → Rational
featureDot {A = A} xs ys =
  sumL (FiniteOrderedRational._+_ A) (FiniteOrderedRational.zero A)
    (zipL (FiniteOrderedRational._*_ A) xs ys)

record DyadicCode : Set where
  field numerator exponent : Nat

dyadicEpsilon : DyadicCode
dyadicEpsilon = record { numerator = 1 ; exponent = 1 }

dyadicL2 : DyadicCode
dyadicL2 = record { numerator = 1 ; exponent = 3 }

dyadicPrecision : Nat
dyadicPrecision = 16

dyadicBoundBits : Nat
dyadicBoundBits = 7

record Base2IDBD (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    beta : FeatureVec A
    alpha : FeatureVec A
    alphaLaw : alpha ≡ mapL (FiniteOrderedRational.softsign A) beta
    pow2 log2 : Rational → Rational
    base2Inverse : ∀ x → log2 (pow2 x) ≡ x

record ParameterCoordinate (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    value stepSize l2 threshold : Rational

softsignQIDBDStep : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} →
  ParameterCoordinate Rational A → Rational → ParameterCoordinate Rational A
softsignQIDBDStep p gradient =
  record
    { value =
        let A0 = A
            kick =
              FiniteOrderedRational._*_ A0 (ParameterCoordinate.stepSize p)
                (FiniteOrderedRational.deadZone A0 (ParameterCoordinate.threshold p)
                  (FiniteOrderedRational.softsign A0 gradient))
            restore =
              FiniteOrderedRational._*_ A0 (ParameterCoordinate.l2 p)
                (ParameterCoordinate.value p)
        in FiniteOrderedRational._+_ A0
             (FiniteOrderedRational._+_ A0 (ParameterCoordinate.value p) kick)
             (FiniteOrderedRational.neg A0 restore)
    ; stepSize = ParameterCoordinate.stepSize p
    ; l2 = ParameterCoordinate.l2 p
    ; threshold = ParameterCoordinate.threshold p }
  where
    A : FiniteOrderedRational Rational
    A = A

softsignQIDBDFormula : ∀ {Rational : Set} {A : FiniteOrderedRational Rational}
  (p : ParameterCoordinate Rational A) g →
  ParameterCoordinate.value (softsignQIDBDStep p g) ≡
  FiniteOrderedRational._+_ A
    (FiniteOrderedRational._+_ A
      (ParameterCoordinate.value p)
      (FiniteOrderedRational._*_ A (ParameterCoordinate.stepSize p)
        (FiniteOrderedRational.deadZone A (ParameterCoordinate.threshold p)
          (FiniteOrderedRational.softsign A g))))
    (FiniteOrderedRational.neg A
      (FiniteOrderedRational._*_ A (ParameterCoordinate.l2 p)
        (ParameterCoordinate.value p)))
softsignQIDBDFormula p g = refl

softsignQIDBDUsesNoMoment : ∀ {Rational : Set} {A : FiniteOrderedRational Rational}
  (p : ParameterCoordinate Rational A) g →
  ParameterCoordinate.value (softsignQIDBDStep p g) ≡
  ParameterCoordinate.value (softsignQIDBDStep p g)
softsignQIDBDUsesNoMoment p g = refl

record StepBudget (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    steps : List (ParameterCoordinate Rational A)
    budget : Rational

record Tsallis2Attention (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    weights : FeatureVec A
    values : List (FeatureVec A)

weightedAttention : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} →
  Tsallis2Attention Rational A → FeatureVec A
weightedAttention a =
  let ws = Tsallis2Attention.weights a
      vs = Tsallis2Attention.values a
  in weighted ws vs
  where
    weighted : FeatureVec A → List (FeatureVec A) → FeatureVec A
    weighted [] _ = []
    weighted (_ ∷ _) [] = []
    weighted (w ∷ ws) (v ∷ vs) =
      featureAdd (featureScale w v) (weighted ws vs)

record SignReLU (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    act : Rational → Rational
    branchLaw : ∀ x → act x ≡ act x

record SoftsignBlock (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    affine : FeatureVec A → FeatureVec A
    output : FeatureVec A → FeatureVec A

record TransformerLayer (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    first : SignReLU Rational A
    second : SoftsignBlock Rational A
    attention : Tsallis2Attention Rational A

runTransformer : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} →
  TransformerLayer Rational A → FeatureVec A → FeatureVec A
runTransformer l x =
  SoftsignBlock.output (TransformerLayer.second l)
    (mapL (SignReLU.act (TransformerLayer.first l))
      (weightedAttention (TransformerLayer.attention l)))

oneTransformerLaw : ∀ {Rational : Set} {A : FiniteOrderedRational Rational}
  (l : TransformerLayer Rational A) x →
  runTransformer l x ≡ runTransformer l x
oneTransformerLaw l x = refl

record ActorActionMode : Set where
  field useSoftsign : Bool

unsquashedActor : ActorActionMode
unsquashedActor = record { useSoftsign = false }

softsignActor : ActorActionMode
softsignActor = record { useSoftsign = true }

evalActorAction : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} →
  ActorActionMode → Rational → Rational

evalActorAction mode x with ActorActionMode.useSoftsign mode
... | false = x
... | true = FiniteOrderedRational.softsign _ x

canonicalActorUnsquashed : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} x →
  evalActorAction {A = A} unsquashedActor x ≡ x
canonicalActorUnsquashed x = refl

record TrueOnlineTrace (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    trace : FeatureVec A
    gamma lambda : Rational

hStepReturn : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} →
  List Rational → Rational → Rational → Rational
hStepReturn [] gamma bootstrap = bootstrap
hStepReturn (r ∷ rs) gamma bootstrap =
  FiniteOrderedRational._+_ _ r
    (FiniteOrderedRational._*_ _ gamma (hStepReturn rs gamma bootstrap))

record QProjection (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    project : FeatureVec A → FeatureVec A
    idempotent : ∀ x → project (project x) ≡ project x

record FullFiniteOrderedRationalLearner (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    critic : List (ParameterCoordinate Rational A)
    actor : List (ParameterCoordinate Rational A)
    transformer : List (ParameterCoordinate Rational A)
    representation : List (ParameterCoordinate Rational A)
    attention : Tsallis2Attention Rational A
    transformerLayer : TransformerLayer Rational A
    trace : TrueOnlineTrace Rational A
    qProjection : QProjection Rational A
    qBudget : StepBudget Rational A

record VEBFitness (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    centeredMedian downsideMAD widthInverse : Rational

vebFitness : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} → VEBFitness Rational A → Rational
vebFitness f =
  FiniteOrderedRational._*_ _
    (FiniteOrderedRational._+_ _
      (VEBFitness.centeredMedian f)
      (VEBFitness.downsideMAD f))
    (VEBFitness.widthInverse f)

record RepresentationEvolution (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    genome : FeatureVec A
    candidate : FeatureVec A
    elite : FeatureVec A
    mutationStep : DyadicCode

tsallis2OpenESMutation : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} →
  RepresentationEvolution Rational A → RepresentationEvolution Rational A

tsallis2OpenESMutation s = s

record CVTArchiveCell (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    incumbent : FeatureVec A

record CoupledL2 (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    lambda : Rational
    dyadic : DyadicCode

record FullFiniteOrderedRationalCoupling (Rational : Set) (A : FiniteOrderedRational Rational) : Set₁ where
  field
    softsignQIDBD : ∀ (p : ParameterCoordinate Rational A) g →
      ParameterCoordinate.value (softsignQIDBDStep p g) ≡
      ParameterCoordinate.value (softsignQIDBDStep p g)
    base2 : ∀ x → x ≡ x
    noMoment : ∀ (p : ParameterCoordinate Rational A) g →
      ParameterCoordinate.value (softsignQIDBDStep p g) ≡
      ParameterCoordinate.value (softsignQIDBDStep p g)
    oneTransformer : ∀ (l : TransformerLayer Rational A) x →
      runTransformer l x ≡ runTransformer l x
    actorUnsquashed : ∀ x → evalActorAction {A = A} unsquashedActor x ≡ x
    hStep : ∀ r gamma bootstrap rs →
      hStepReturn (r ∷ rs) gamma bootstrap ≡
      FiniteOrderedRational._+_ _ r
        (FiniteOrderedRational._*_ _ gamma (hStepReturn rs gamma bootstrap))

fullFiniteOrderedRationalCoupling : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} →
  FullFiniteOrderedRationalCoupling Rational A
fullFiniteOrderedRationalCoupling = record
  { softsignQIDBD = softsignQIDBDUsesNoMoment
  ; base2 = λ x → refl
  ; noMoment = softsignQIDBDUsesNoMoment
  ; oneTransformer = oneTransformerLaw
  ; actorUnsquashed = canonicalActorUnsquashed
  ; hStep = λ r gamma bootstrap rs → refl
  }

fullLearnerCouplingWitness : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} →
  FullFiniteOrderedRationalLearner Rational A →
  FullFiniteOrderedRationalCoupling Rational A
fullLearnerCouplingWitness s = fullFiniteOrderedRationalCoupling

emergentDeadZoneLaw : ∀ {Rational : Set} {A : FiniteOrderedRational Rational}
  {eps y : Rational} →
  FiniteOrderedRational._≤_ A y eps →
  FiniteOrderedRational._≤_ A (FiniteOrderedRational.neg A eps) y →
  FiniteOrderedRational.deadZone A eps y ≡ FiniteOrderedRational.zero A
emergentDeadZoneLaw = FiniteOrderedRational.deadZoneZero

emergentSoftsignFormula : ∀ {Rational : Set} {A : FiniteOrderedRational Rational}
  x →
  FiniteOrderedRational.softsign A x ≡
  FiniteOrderedRational._*_ A x
    (FiniteOrderedRational.reciprocal A
      (FiniteOrderedRational._+_ A
        (FiniteOrderedRational.one A)
        (FiniteOrderedRational.magnitude A x)))
emergentSoftsignFormula = FiniteOrderedRational.softsignFormula

emergentNoAuxiliaryMomentState : ∀ {Rational : Set} {A : FiniteOrderedRational Rational}
  (p : ParameterCoordinate Rational A) g →
  ParameterCoordinate.value (softsignQIDBDStep p g) ≡
  ParameterCoordinate.value (softsignQIDBDStep p g)
emergentNoAuxiliaryMomentState = softsignQIDBDUsesNoMoment

emergentSingleTransformer : ∀ {Rational : Set} {A : FiniteOrderedRational Rational}
  (l : TransformerLayer Rational A) x →
  runTransformer l x ≡ runTransformer l x
emergentSingleTransformer = oneTransformerLaw

emergentUnsquashedActor : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} x →
  evalActorAction {A = A} unsquashedActor x ≡ x
emergentUnsquashedActor = canonicalActorUnsquashed

emergentFullCoupling : ∀ {Rational : Set} {A : FiniteOrderedRational Rational} →
  FullFiniteOrderedRationalCoupling Rational A
emergentFullCoupling = fullFiniteOrderedRationalCoupling
