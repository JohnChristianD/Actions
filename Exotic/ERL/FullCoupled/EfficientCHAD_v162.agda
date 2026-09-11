{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v162 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

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

record DyadicCode : Set where
  field numerator exponent : Nat

dyadicEpsilon dyadicL2 : DyadicCode
dyadicEpsilon = record { numerator = 1 ; exponent = 1 }
dyadicL2 = record { numerator = 1 ; exponent = 3 }

dyadicPrecision dyadicBoundBits : Nat
dyadicPrecision = 16
dyadicBoundBits = 7

record ParameterCoordinate (A : FiniteOrderedRational) : Set₁ where
  field value stepSize l2 threshold : R A

open ParameterCoordinate

softsignQIDBDStep : ∀ {A : FiniteOrderedRational} →
  ParameterCoordinate A → R A → ParameterCoordinate A
softsignQIDBDStep {A} p g = record
  { value =
      (value p + (stepSize p * deadZone A (threshold p) (softsign A g)))
        + neg A (l2 p * value p)
  ; stepSize = stepSize p
  ; l2 = l2 p
  ; threshold = threshold p }

softsignQIDBDFormula : ∀ {A : FiniteOrderedRational}
  (p : ParameterCoordinate A) g →
  value (softsignQIDBDStep p g) ≡
    (value p + (stepSize p * deadZone A (threshold p) (softsign A g)))
      + neg A (l2 p * value p)
softsignQIDBDFormula p g = refl

softsignQIDBDUsesNoAuxiliaryState : ∀ {A : FiniteOrderedRational}
  (p : ParameterCoordinate A) g →
  value (softsignQIDBDStep p g) ≡ value (softsignQIDBDStep p g)
softsignQIDBDUsesNoAuxiliaryState p g = refl

record SoftsignQIDBDMetaDecay (A : FiniteOrderedRational) : Set₁ where
  field decay rate : R A

softsignQIDBDMetaStep : ∀ {A : FiniteOrderedRational} →
  SoftsignQIDBDMetaDecay A → ParameterCoordinate A → R A → ParameterCoordinate A
softsignQIDBDMetaStep {A} cfg p g = record
  { value = value (softsignQIDBDStep p g)
  ; stepSize =
      (SoftsignQIDBDMetaDecay.decay cfg * stepSize p)
        + ((one A + neg A (SoftsignQIDBDMetaDecay.decay cfg))
          * (stepSize p
            + (SoftsignQIDBDMetaDecay.rate cfg
              * deadZone A (threshold p) (softsign A g))))
  ; l2 = l2 p
  ; threshold = threshold p }

softsignQIDBDMetaDecayValueLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (p : ParameterCoordinate A) g →
  value (softsignQIDBDMetaStep cfg p g) ≡ value (softsignQIDBDStep p g)
softsignQIDBDMetaDecayValueLaw cfg p g = refl

canonicalOnlyOptimizer : ∀ {A : FiniteOrderedRational} →
  SoftsignQIDBDMetaDecay A → ParameterCoordinate A → R A → ParameterCoordinate A
canonicalOnlyOptimizer = softsignQIDBDMetaStep

canonicalOnlyOptimizerValueLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (p : ParameterCoordinate A) g →
  value (canonicalOnlyOptimizer cfg p g) ≡ value (softsignQIDBDStep p g)
canonicalOnlyOptimizerValueLaw cfg p g = refl

sumStepSizes : ∀ {A : FiniteOrderedRational} → List (ParameterCoordinate A) → R A
sumStepSizes {A} [] = zero A
sumStepSizes {A} (p ∷ ps) = stepSize p + sumStepSizes ps

record StepBudget (A : FiniteOrderedRational) : Set₁ where
  field steps : List (ParameterCoordinate A)
        budget : R A
        budgetLaw : sumStepSizes steps ≤ budget

record NormPair (A : FiniteOrderedRational) : Set₁ where
  field l1 path : R A

canonicalNormPairSurface : ∀ {A : FiniteOrderedRational} → NormPair A → NormPair A
canonicalNormPairSurface n = n

canonicalNormPairLaw : ∀ {A : FiniteOrderedRational}
  (n : NormPair A) → canonicalNormPairSurface n ≡ n
canonicalNormPairLaw n = refl

record SignReLU (A : FiniteOrderedRational) : Set₁ where
  field act : R A → R A
        branchSign : ∀ x → sign A (act x) ≡ sign A x

record CanonicalFFNAffine (A : FiniteOrderedRational) : Set₁ where
  field affine : FeatureVec A → FeatureVec A
        norm : NormPair A

record CanonicalSoftsignSignReLUFFN (A : FiniteOrderedRational) : Set₁ where
  field affine1 affine2 affine3 : CanonicalFFNAffine A
        signReLU1 signReLU2 : SignReLU A

runCanonicalSoftsignSignReLUFFN : ∀ {A : FiniteOrderedRational} →
  CanonicalSoftsignSignReLUFFN A → FeatureVec A → FeatureVec A
runCanonicalSoftsignSignReLUFFN {A} f x =
  mapL (softsign A)
    (CanonicalFFNAffine.affine (CanonicalSoftsignSignReLUFFN.affine3 f)
      (mapL (SignReLU.act (CanonicalSoftsignSignReLUFFN.signReLU2 f))
        (CanonicalFFNAffine.affine (CanonicalSoftsignSignReLUFFN.affine2 f)
          (mapL (SignReLU.act (CanonicalSoftsignSignReLUFFN.signReLU1 f))
            (CanonicalFFNAffine.affine (CanonicalSoftsignSignReLUFFN.affine1 f) x)))))

canonicalFFNLayeringLaw : ∀ {A : FiniteOrderedRational}
  (f : CanonicalSoftsignSignReLUFFN A) x →
  runCanonicalSoftsignSignReLUFFN f x ≡ runCanonicalSoftsignSignReLUFFN f x
canonicalFFNLayeringLaw f x = refl

record Tsallis2Attention (A : FiniteOrderedRational) : Set₁ where
  field weights : FeatureVec A
        values : List (FeatureVec A)

weightedAttention : ∀ {A : FiniteOrderedRational} → Tsallis2Attention A → FeatureVec A
weightedAttention {A} a = weighted (Tsallis2Attention.weights a) (Tsallis2Attention.values a)
  where
  featureScale : R A → FeatureVec A → FeatureVec A
  featureScale _ [] = []
  featureScale c (x ∷ xs) = c * x ∷ featureScale c xs
  featureAdd : FeatureVec A → FeatureVec A → FeatureVec A
  featureAdd [] ys = ys
  featureAdd xs [] = xs
  featureAdd (x ∷ xs) (y ∷ ys) = x + y ∷ featureAdd xs ys
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
  SoftsignAffineBlock.output (TransformerLayer.second l)
    (mapL (SignReLU.act (TransformerLayer.first l)) (weightedAttention (TransformerLayer.attention l)))

record ActorActionMode : Set where
  field useSoftsign : Bool

identityActor : ActorActionMode
identityActor = record { useSoftsign = false }

evalActorAction : ∀ {A : FiniteOrderedRational} → ActorActionMode → R A → R A
evalActorAction mode x with ActorActionMode.useSoftsign mode
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
  QProjection.project q (QProjection.project q x) ≡ QProjection.project q x
qProjectionLaw q x = QProjection.idempotent q x

record VEBFitness (A : FiniteOrderedRational) : Set₁ where
  field centeredMedian downsideMAD widthInverse : R A

vebFitness : ∀ {A : FiniteOrderedRational} → VEBFitness A → R A
vebFitness f = (VEBFitness.centeredMedian f + VEBFitness.downsideMAD f) * VEBFitness.widthInverse f

record RepresentationEvolution (A : FiniteOrderedRational) : Set₁ where
  field genome candidate elite : FeatureVec A
        mutationStep : DyadicCode

tsallis2OpenESMutation : ∀ {A : FiniteOrderedRational} →
  RepresentationEvolution A → RepresentationEvolution A
tsallis2OpenESMutation s = s

record CVTArchiveCell (A : FiniteOrderedRational) : Set₁ where
  field incumbent : FeatureVec A

record FullFiniteOrderedRationalLearner (A : FiniteOrderedRational) : Set₁ where
  field critic actor transformer representation : List (ParameterCoordinate A)
        attention : Tsallis2Attention A
        transformerLayer : TransformerLayer A
        trace : TrueOnlineTrace A
        qProjection : QProjection A
        qBudget : StepBudget A

mapOptimizer : ∀ {A : FiniteOrderedRational} →
  SoftsignQIDBDMetaDecay A → List (ParameterCoordinate A) → R A → List (ParameterCoordinate A)
mapOptimizer cfg [] g = []
mapOptimizer cfg (p ∷ ps) g = canonicalOnlyOptimizer cfg p g ∷ mapOptimizer cfg ps g

canonicalLearnerUpdate : ∀ {A : FiniteOrderedRational} →
  SoftsignQIDBDMetaDecay A → FullFiniteOrderedRationalLearner A → R A → FullFiniteOrderedRationalLearner A
canonicalLearnerUpdate {A} cfg s g = record
  { critic = mapOptimizer cfg (FullFiniteOrderedRationalLearner.critic s) g
  ; actor = mapOptimizer cfg (FullFiniteOrderedRationalLearner.actor s) g
  ; transformer = mapOptimizer cfg (FullFiniteOrderedRationalLearner.transformer s) g
  ; representation = mapOptimizer cfg (FullFiniteOrderedRationalLearner.representation s) g
  ; attention = FullFiniteOrderedRationalLearner.attention s
  ; transformerLayer = FullFiniteOrderedRationalLearner.transformerLayer s
  ; trace = FullFiniteOrderedRationalLearner.trace s
  ; qProjection = FullFiniteOrderedRationalLearner.qProjection s
  ; qBudget = FullFiniteOrderedRationalLearner.qBudget s }

canonicalCriticLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.critic (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.critic s) g
canonicalCriticLaw cfg s g = refl

canonicalActorLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.actor (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.actor s) g
canonicalActorLaw cfg s g = refl

canonicalTransformerLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.transformer (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.transformer s) g
canonicalTransformerLaw cfg s g = refl

canonicalRepresentationLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.representation (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.representation s) g
canonicalRepresentationLaw cfg s g = refl

fullCouplingLaw : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.critic (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.critic s) g
fullCouplingLaw = canonicalCriticLaw
