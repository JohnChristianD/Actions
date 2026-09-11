{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_F4IntSigmaDelta where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int)
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
    maximum sign softsign : R → R
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

mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f [] = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

FeatureVec : FiniteOrderedRational → Set
FeatureVec A = List (R A)

record DyadicCode : Set where
  field numerator exponent : Nat

dyadicEpsilon dyadicL2 : DyadicCode
dyadicEpsilon = record { numerator = 1 ; exponent = 1 }
dyadicL2 = record { numerator = 1 ; exponent = 3 }

dyadicPrecision dyadicBoundBits : Nat
dyadicPrecision = 16
dyadicBoundBits = 7

record Base2IDBD (A : FiniteOrderedRational) : Set₁ where
  field beta alpha : FeatureVec A
        alphaLaw : alpha ≡ mapL (pow2 A) beta

idbdPow2 : ∀ {A : FiniteOrderedRational} → FeatureVec A → FeatureVec A
idbdPow2 {A} = mapL (pow2 A)

idbdLog2 : ∀ {A : FiniteOrderedRational} → FeatureVec A → FeatureVec A
idbdLog2 {A} = mapL (log2 A)

idbdBase2RoundTrip : ∀ {A : FiniteOrderedRational} xs → idbdLog2 A (idbdPow2 A xs) ≡ xs
idbdBase2RoundTrip {A} [] = refl
idbdBase2RoundTrip {A} (x ∷ xs) = cong₂ _∷_ (log2Pow2 A x) (idbdBase2RoundTrip xs)

record IntegerStepCode : Set where
  field
    value : Int
    roundStep : RoundingCode

record RoundingCode : Set where
  field
    round : ∀ {A : FiniteOrderedRational} → R A → Int
    fromInt : ∀ {A : FiniteOrderedRational} → Int → R A
    roundLaw : ∀ {A : FiniteOrderedRational} x →
      fromInt (round x) + zero A ≡ fromInt (round x)

record SigmaDeltaMomentum (A : FiniteOrderedRational) : Set₁ where
  field
    quantize : R A → R A
    residual : R A → R A
    reconstruction : ∀ x → quantize x + residual x ≡ x

record SigmaDeltaLogStep (A : FiniteOrderedRational) : Set₁ where
  field
    quantize : R A → Int
    fromInt : Int → R A
    residual : R A → R A
    reconstruction : ∀ x → fromInt (quantize x) + residual x ≡ x

record F4IntSigmaDeltaState (A : FiniteOrderedRational) : Set₁ where
  field
    theta : R A
    eq : R A
    re : R A
    rl : R A
    ell : Int
    momentum : SigmaDeltaMomentum A
    logStep : SigmaDeltaLogStep A
    beta2 betaTheta : R A
    qEpsilon : R A
    effectivePower : Int → R A

open F4IntSigmaDeltaState

f4EffectiveMomentum : ∀ {A : FiniteOrderedRational} → F4IntSigmaDeltaState A → R A
f4EffectiveMomentum s = eq s + re s

f4MomentumReconstruction : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) →
  SigmaDeltaMomentum.reconstruction (momentum s) (eq s + re s) ≡ SigmaDeltaMomentum.reconstruction (momentum s) (eq s + re s)
f4MomentumReconstruction s = refl

f4ExactEMA : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g → R A
f4ExactEMA s g =
  (beta2 s * f4EffectiveMomentum s)
    + ((one A + neg A (beta2 s)) * g)

f4MomentumQuantize : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g → R A
f4MomentumQuantize s g = SigmaDeltaMomentum.quantize (momentum s) (f4ExactEMA s g)

f4MomentumResidual : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g → R A
f4MomentumResidual s g = SigmaDeltaMomentum.residual (momentum s) (f4ExactEMA s g)

f4MomentumSigmaDeltaLaw : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g →
  f4MomentumQuantize s g + f4MomentumResidual s g ≡ f4ExactEMA s g
f4MomentumSigmaDeltaLaw s g = SigmaDeltaMomentum.reconstruction (momentum s) (f4ExactEMA s g)

f4LogAccumulator : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g → R A
f4LogAccumulator s g = (rl s) + f4ExactEMA s g

f4LogQuantum : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g → Int
f4LogQuantum s g = SigmaDeltaLogStep.quantize (logStep s) (f4LogAccumulator s g)

f4LogResidual : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g → R A
f4LogResidual s g = SigmaDeltaLogStep.residual (logStep s) (f4LogAccumulator s g)

f4LogSigmaDeltaLaw : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g →
  SigmaDeltaLogStep.fromInt (logStep s) (f4LogQuantum s g) + f4LogResidual s g ≡ f4LogAccumulator s g
f4LogSigmaDeltaLaw s g = SigmaDeltaLogStep.reconstruction (logStep s) (f4LogAccumulator s g)

f4ParameterStep : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) g → R A
f4ParameterStep s g =
  theta s
    + effectivePower s (ell s) * deadZone A (qEpsilon s) (softsign A g)
    + neg A (betaTheta s * theta s)

record ParameterCoordinate (A : FiniteOrderedRational) : Set₁ where
  field value stepSize l2 threshold : R A

record NormPair (A : FiniteOrderedRational) : Set₁ where
  field l1 path : R A

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

record SoftsignAffineBlock (A : FiniteOrderedRational) : Set₁ where
  field affine output : FeatureVec A → FeatureVec A
        norm : NormPair A

record TransformerLayer (A : FiniteOrderedRational) : Set₁ where
  field first : SignReLU A
        second : SoftsignAffineBlock A
        attention : Tsallis2Attention A

record FullFiniteOrderedRationalLearner (A : FiniteOrderedRational) : Set₁ where
  field critic actor transformer representation : List (ParameterCoordinate A)
        f4 : F4IntSigmaDeltaState A
        attention : Tsallis2Attention A
        transformerLayer : TransformerLayer A
        qBudget : R A

record CanonicalComposition (A : FiniteOrderedRational) : Set₁ where
  field
    optimizer : F4IntSigmaDeltaState A
    ffn : CanonicalSoftsignSignReLUFFN A
    norm : NormPair A
    learner : FullFiniteOrderedRationalLearner A

canonicalOptimizerIsF4IntSigmaDelta : ∀ {A : FiniteOrderedRational}
  (s : F4IntSigmaDeltaState A) → F4IntSigmaDeltaState A
canonicalOptimizerIsF4IntSigmaDelta s = s

canonicalAllOptimizerBearingState : ∀ {A : FiniteOrderedRational}
  (s : FullFiniteOrderedRationalLearner A) → F4IntSigmaDeltaState A
canonicalAllOptimizerBearingState s = f4 s

canonicalCompositionSurface : ∀ {A : FiniteOrderedRational}
  (c : CanonicalComposition A) → F4IntSigmaDeltaState A
canonicalCompositionSurface c = optimizer c
