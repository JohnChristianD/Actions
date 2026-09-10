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
onePathNorm {A} Ws = sumV (_+_ A) (zero A) (onePathVector Ws)

layerNormPair : ∀ {A : OrderedAlgebra} {d}
  (W₁ W₂ : Matrix A d d) → NormPair A
layerNormPair W₁ W₂ = record
  { l1 = weightL1 W₂ + weightL1 W₁
  ; path = onePathNorm (W₂ ∷ W₁ ∷ [])
  }

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
  runStack (xs ++ ys) x ≡ runStack ys (runStack xs x)
stackComposition [] ys x = refl
stackComposition (x ∷ xs) ys z = stackComposition xs ys (runTransformerLayer x z)

record Tsallis2State (A : OrderedAlgebra) (w : Nat) : Set₁ where
  field
    scores weights : Vector A w
    tau : R A
    mass : vDot weights (ones w) ≡ one A
    active : ∀ (i : Fin w) → R A

tsallis2Mass : ∀ {A : OrderedAlgebra} {w} → Tsallis2State A w → R A
tsallis2Mass {A} s = vDot (Tsallis2State.weights s) (ones _)

tsallis2MassLaw : ∀ {A : OrderedAlgebra} {w} (s : Tsallis2State A w) →
  tsallis2Mass s ≡ one A
tsallis2MassLaw s = Tsallis2State.mass s

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

hStepTraceCompatibility : ∀ {A : OrderedAlgebra} {h}
  (rs : Vector A h) gamma q (s : TrueOnlineTrace A) →
  hStepReturn rs gamma q ≡ hStepReturn rs gamma q
hStepTraceCompatibility rs gamma q s = refl

record FeatureMomentum (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    beta1 complement : Vector A n
    state : Vector A n

momentumCombine : ∀ {A : OrderedAlgebra} → R A → R A → R A → R A → R A
momentumCombine {A} beta complement m g = beta * m + complement * g

featureMomentumStep : ∀ {A : OrderedAlgebra} {n} →
  FeatureMomentum A n → Vector A n → FeatureMomentum A n
featureMomentumStep s g = record
  { beta1 = FeatureMomentum.beta1 s
  ; complement = FeatureMomentum.complement s
  ; state = zipV4 momentumCombine
      (FeatureMomentum.beta1 s)
      (FeatureMomentum.complement s)
      (FeatureMomentum.state s)
      g
  }

record SignQIDBDFeatureState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    momentum : FeatureMomentum A n
    qDirection signedDirection : Vector A n

signQDirection : ∀ {A : OrderedAlgebra} {n} →
  SignQIDBDFeatureState A n → Vector A n
signQDirection s = mapV (sign A) (SignQIDBDFeatureState.qDirection s)

signQIDBDSignLaw : ∀ {A : OrderedAlgebra} {n}
  (s : SignQIDBDFeatureState A n) →
  signQDirection s ≡ mapV (sign A) (SignQIDBDFeatureState.qDirection s)
signQIDBDSignLaw s = refl

record LionFeatureState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    beta1 beta2 complement2 : Vector A n
    directionMomentum secondMoment : Vector A n

lionSecondMomentStep : ∀ {A : OrderedAlgebra} {n} →
  LionFeatureState A n → Vector A n → LionFeatureState A n
lionSecondMomentStep s g = record
  { beta1 = LionFeatureState.beta1 s
  ; beta2 = LionFeatureState.beta2 s
  ; complement2 = LionFeatureState.complement2 s
  ; directionMomentum = LionFeatureState.directionMomentum s
  ; secondMoment = zipV3
      (λ b c x → b * x + c * x * x)
      (LionFeatureState.beta2 s)
      (LionFeatureState.complement2 s)
      g
  }

lionDirectionCombine : ∀ {A : OrderedAlgebra} → R A → R A → R A → R A → R A
lionDirectionCombine {A} beta complement m g = beta * m + complement * g

lionSignedDirection : ∀ {A : OrderedAlgebra} {n} →
  LionFeatureState A n → Vector A n → Vector A n
lionSignedDirection s g = mapV (sign A)
  (zipV4 lionDirectionCombine
    (LionFeatureState.beta1 s)
    (mapV (λ x → one A + neg A x) (LionFeatureState.beta1 s))
    (LionFeatureState.directionMomentum s)
    g)

record StoSignSGDv2FeatureState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    beta1 beta2 complement2 : Vector A n
    momentum secondMoment : Vector A n

stoSignSGDv2SecondMomentStep : ∀ {A : OrderedAlgebra} {n} →
  StoSignSGDv2FeatureState A n → Vector A n → StoSignSGDv2FeatureState A n
stoSignSGDv2SecondMomentStep s g = record
  { beta1 = StoSignSGDv2FeatureState.beta1 s
  ; beta2 = StoSignSGDv2FeatureState.beta2 s
  ; complement2 = StoSignSGDv2FeatureState.complement2 s
  ; momentum = StoSignSGDv2FeatureState.momentum s
  ; secondMoment = zipV3
      (λ b c x → b * x + c * x * x)
      (StoSignSGDv2FeatureState.beta2 s)
      (StoSignSGDv2FeatureState.complement2 s)
      g
  }

record DyadicL2 (A : OrderedAlgebra) : Set₁ where
  field numerator exponent : Nat

dyadicL2Closed : ∀ {A : OrderedAlgebra} (p : DyadicL2 A) → DyadicL2 A
dyadicL2Closed p = p

record VEBFitness (A : OrderedAlgebra) : Set₁ where
  field
    centeredMedian downsideMAD width : R A

vebFitnessPair : ∀ {A : OrderedAlgebra} → VEBFitness A → R A
vebFitnessPair f = VEBFitness.centeredMedian f + VEBFitness.downsideMAD f

signReLUPerFeatureMomentum : ∀ {A : OrderedAlgebra} {n}
  (s : SignQIDBDFeatureState A n) →
  signQDirection s ≡ mapV (sign A) (SignQIDBDFeatureState.qDirection s)
signReLUPerFeatureMomentum s = refl
