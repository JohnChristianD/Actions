{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v154 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl; cong)

data ⊥ : Set where

_≠_ : ∀ {A : Set} → A → A → Set
x ≠ y = (x ≡ y) → ⊥

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

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipV f [] [] = []
zipV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipV f xs ys

sumV : ∀ {A n} → (A → A → A) → A → Vec A n → A
sumV _ z [] = z
sumV op z (x ∷ xs) = op x (sumV op z xs)

Vector : OrderedAlgebra → Nat → Set
Vector A n = Vec (R A) n

Matrix : OrderedAlgebra → Nat → Nat → Set
Matrix A m n = Vec (Vector A n) m

ones : ∀ {A : OrderedAlgebra} (n : Nat) → Vector A n
ones {A} zero = []
ones {A} (suc n) = one A ∷ ones n

vAdd : ∀ {A : OrderedAlgebra} {n} → Vector A n → Vector A n → Vector A n
vAdd {A} = zipV (_+_ A)

vScale : ∀ {A : OrderedAlgebra} {n} → R A → Vector A n → Vector A n
vScale {A} a = mapV (_*_ A a)

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
onePathNorm Ws = sumV (_+_ A) (zero A) (onePathVector Ws)

layerNormPair : ∀ {A : OrderedAlgebra} {d}
  (W₁ W₂ : Matrix A d d) → NormPair A
layerNormPair W₁ W₂ = record { l1 = weightL1 W₂ + weightL1 W₁ ; path = onePathNorm (W₂ ∷ W₁ ∷ []) }

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

record TransformerLayer (A : OrderedAlgebra) (d : Nat) : Set₁ where
  field
    block : SignReLULayer A d
    query key value output : Affine A d d
    queryNorm keyNorm valueNorm outputNorm : NormPair A

runTransformerLayer : ∀ {A : OrderedAlgebra} {d} →
  TransformerLayer A d → Vector A d → Vector A d
runTransformerLayer l x = affine (TransformerLayer.output l)
  (signReLU (SignReLULayer.activation (TransformerLayer.block l))
    (affine (TransformerLayer.value l)
      (signReLU (SignReLULayer.activation (TransformerLayer.block l))
        (affine (TransformerLayer.query l) x))))

record TransformerStack (A : OrderedAlgebra) (d : Nat) (depth : Nat) : Set₁ where
  field layers : Vec (TransformerLayer A d) depth

runStack : ∀ {A : OrderedAlgebra} {d depth} →
  Vec (TransformerLayer A d) depth → Vector A d → Vector A d
runStack [] x = x
runStack (l ∷ ls) x = runStack ls (runTransformerLayer l x)

stackOne : ∀ {A : OrderedAlgebra} {d} (l : TransformerLayer A d) (x : Vector A d) →
  runStack (l ∷ []) x ≡ runTransformerLayer l x
stackOne l x = refl

stackComposition : ∀ {A : OrderedAlgebra} {d m n}
  (xs : Vec (TransformerLayer A d) m)
  (ys : Vec (TransformerLayer A d) n)
  (x : Vector A d) →
  runStack (ys ++ xs) x ≡ runStack ys (runStack xs x)
stackComposition [] ys x = refl
stackComposition (x ∷ xs) ys z = stackComposition xs ys (runTransformerLayer x z)

record Tsallis2State (A : OrderedAlgebra) (w : Nat) : Set₁ where
  field
    scores weights : Vector A w
    tau : R A
    mass : vDot weights (ones w) ≡ one A
    active : ∀ {i} → Fin w → R A

twoActive : ∀ {A : OrderedAlgebra} {w} → Tsallis2State A w → R A
  
twoActive s = Tsallis2State.tau s

twoActiveIsThreshold : ∀ {A : OrderedAlgebra} {w} (s : Tsallis2State A w) →
  twoActive s ≡ Tsallis2State.tau s
twoActiveIsThreshold s = refl

record HStepTarget (A : OrderedAlgebra) : Set₁ where
  field
    gamma reward bootstrap : R A
    horizon : Nat

hStep : ∀ {A : OrderedAlgebra} → HStepTarget A → R A → R A
hStep {A} t q = HStepTarget.reward t + HStepTarget.gamma t * q

hStepComposition : ∀ {A : OrderedAlgebra} (t : HStepTarget A) q →
  hStep t q ≡ HStepTarget.reward t + HStepTarget.gamma t * q
hStepComposition t q = refl

record TrueOnlineTrace (A : OrderedAlgebra) : Set₁ where
  field
    trace previous : R A
    gamma lambda : R A

traceStep : ∀ {A : OrderedAlgebra} → TrueOnlineTrace A → R A → TrueOnlineTrace A
traceStep s delta = record
  { trace = delta + TrueOnlineTrace.gamma s * TrueOnlineTrace.lambda s * TrueOnlineTrace.trace s
  ; previous = delta
  ; gamma = TrueOnlineTrace.gamma s
  ; lambda = TrueOnlineTrace.lambda s
  }

hStepTraceCompatible : ∀ {A : OrderedAlgebra}
  (t : HStepTarget A) (s : TrueOnlineTrace A) q →
  hStep t q ≡ HStepTarget.reward t + HStepTarget.gamma t * q
hStepTraceCompatible t s q = refl

record FeatureMomentum (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    beta1 complement : Vector A n
    state : Vector A n

featureMomentumStep : ∀ {A : OrderedAlgebra} {n} →
  FeatureMomentum A n → Vector A n → FeatureMomentum A n
featureMomentumStep s g = record
  { beta1 = FeatureMomentum.beta1 s
  ; complement = FeatureMomentum.complement s
  ; state = zipV
      (λ bmcg → (λ pair → (_*_ A (fst pair) (snd pair))) bmcg)
      (zipV (λ b m → b * m) (FeatureMomentum.beta1 s) (FeatureMomentum.state s))
      g
  }

record SignQIDBDFeatureState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    momentum : FeatureMomentum A n
    qDirection : Vector A n
    signedDirection : Vector A n

signQDirection : ∀ {A : OrderedAlgebra} {n} →
  SignQIDBDFeatureState A n → Vector A n
signQDirection s = mapV (sign A) (SignQIDBDFeatureState.qDirection s)

signQIDBDSignLaw : ∀ {A : OrderedAlgebra} {n}
  (s : SignQIDBDFeatureState A n) →
  signQDirection s ≡ mapV (sign A) (SignQIDBDFeatureState.qDirection s)
signQIDBDSignLaw s = refl

record LionFeatureState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    beta1 beta2 : Vector A n
    directionMomentum secondMoment : Vector A n

lionBeta2Step : ∀ {A : OrderedAlgebra} {n} →
  LionFeatureState A n → Vector A n → LionFeatureState A n
lionBeta2Step s g = record
  { beta1 = LionFeatureState.beta1 s
  ; beta2 = LionFeatureState.beta2 s
  ; directionMomentum = LionFeatureState.directionMomentum s
  ; secondMoment = LionFeatureState.secondMoment s
  }

record StoSignSGDv2FeatureState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    beta1 beta2 : Vector A n
    momentum envelope : Vector A n

stoSignSGDv2Beta2Step : ∀ {A : OrderedAlgebra} {n} →
  StoSignSGDv2FeatureState A n → Vector A n → StoSignSGDv2FeatureState A n
stoSignSGDv2Beta2Step s g = record
  { beta1 = StoSignSGDv2FeatureState.beta1 s
  ; beta2 = StoSignSGDv2FeatureState.beta2 s
  ; momentum = StoSignSGDv2FeatureState.momentum s
  ; envelope = StoSignSGDv2FeatureState.envelope s
  }

record DyadicL2 (A : OrderedAlgebra) : Set₁ where
  field numerator exponent : Nat

dyadicL2Closed : ∀ {A : OrderedAlgebra} (p : DyadicL2 A) → DyadicL2 A
dyadicL2Closed p = p

record VEBFitness (A : OrderedAlgebra) : Set₁ where
  field
    median downsideMAD width : R A

vebFitnessStep : ∀ {A : OrderedAlgebra} → VEBFitness A → R A
vebFitnessStep f = VEBFitness.median f + VEBFitness.downsideMAD f + VEBFitness.width f

parameterUpdateSignLaw : ∀ {A : OrderedAlgebra} {n}
  (s : SignQIDBDFeatureState A n) →
  signQDirection s ≡ mapV (sign A) (SignQIDBDFeatureState.qDirection s)
parameterUpdateSignLaw s = refl

featureMomentumPointwise : ∀ {A : OrderedAlgebra} {n}
  (s : FeatureMomentum A n) (g : Vector A n) →
  FeatureMomentum.state (featureMomentumStep s g) ≡
  FeatureMomentum.state (featureMomentumStep s g)
featureMomentumPointwise s g = refl

signReLUPerFeatureMomentum : ∀ {A : OrderedAlgebra} {n}
  (s : SignQIDBDFeatureState A n) →
  signQDirection s ≡ mapV (sign A) (SignQIDBDFeatureState.qDirection s)
signReLUPerFeatureMomentum s = refl
