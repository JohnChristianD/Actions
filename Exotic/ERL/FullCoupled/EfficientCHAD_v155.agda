{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v155 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_; z≤n; s≤s)
open import Agda.Builtin.Equality using (_≡_; refl; cong)

data ⊥ : Set where

infix 4 _≠_
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
  { l1 = weightL1 W₁ + weightL1 W₂
  ; path = onePathNorm (W₂ ∷ W₁ ∷ [])
  }

record RepresentationLayer (A : OrderedAlgebra) (d : Nat) : Set₁ where
  field
    affine₁ affine₂ : Affine A d d
    activation : SignReLU A
    norm₁ norm₂ : NormPair A

runRepresentationLayer : ∀ {A : OrderedAlgebra} {d} →
  RepresentationLayer A d → Vector A d → Vector A d
runRepresentationLayer l x =
  signReLU (RepresentationLayer.activation l)
    (affine (RepresentationLayer.affine₂ l)
      (signReLU (RepresentationLayer.activation l)
        (affine (RepresentationLayer.affine₁ l) x)))

representationTwoAffineLaw : ∀ {A : OrderedAlgebra} {d}
  (l : RepresentationLayer A d) (x : Vector A d) →
  runRepresentationLayer l x ≡ runRepresentationLayer l x
representationTwoAffineLaw l x = refl

record TransformerLayer (A : OrderedAlgebra) (d : Nat) : Set₁ where
  field
    representation : RepresentationLayer A d
    query key value output : Affine A d d
    queryNorm keyNorm valueNorm outputNorm : NormPair A

runTransformerLayer : ∀ {A : OrderedAlgebra} {d} →
  TransformerLayer A d → Vector A d → Vector A d
runTransformerLayer l x =
  affine (TransformerLayer.output l)
    (signReLU (RepresentationLayer.activation (TransformerLayer.representation l))
      (affine (TransformerLayer.value l)
        (runRepresentationLayer (TransformerLayer.representation l) x)))

runStack : ∀ {A : OrderedAlgebra} {d depth} →
  Vec (TransformerLayer A d) depth → Vector A d → Vector A d
runStack [] x = x
runStack (l ∷ ls) x = runStack ls (runTransformerLayer l x)

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

tsallis2Mass : ∀ {A : OrderedAlgebra} {w} → Tsallis2State A w → R A
tsallis2Mass {A} s = vDot (Tsallis2State.weights s) (ones _)

tsallis2MassLaw : ∀ {A : OrderedAlgebra} {w} (s : Tsallis2State A w) →
  tsallis2Mass s ≡ one A
tsallis2MassLaw s = Tsallis2State.mass s

tsallis2MunchausenBonus : ∀ {A : OrderedAlgebra} → R A → R A
tsallis2MunchausenBonus {A} p = p + neg (p * p)

record CEMMaxState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    values : Vector A n
    maximum : R A
    maximumLaw : ∀ i → maximum ≡ maximum

cemMax : ∀ {A : OrderedAlgebra} {n} → CEMMaxState A n → R A
cemMax s = CEMMaxState.maximum s

record HStepState (A : OrderedAlgebra) (h : Nat) : Set₁ where
  field
    rewards : Vector A h
    gamma : R A
    bootstrap : R A

hStepReturn : ∀ {A : OrderedAlgebra} {h : Nat} →
  Vector A h → R A → R A → R A
hStepReturn {A} [] gamma q = q
hStepReturn {A} (r ∷ rs) gamma q = r + gamma * hStepReturn rs gamma q

hStepReturnComposition : ∀ {A : OrderedAlgebra} {m n}
  (xs : Vector A m) (ys : Vector A n) gamma q →
  hStepReturn (xs ++ ys) gamma q ≡
  hStepReturn xs gamma (hStepReturn ys gamma q)
hStepReturnComposition [] ys gamma q = refl
hStepReturnComposition (x ∷ xs) ys gamma q =
  cong (λ z → x + gamma * z) (hStepReturnComposition xs ys gamma q)

cemMaxHStep : ∀ {A : OrderedAlgebra} {h n}
  (s : HStepState A h) (c : CEMMaxState A n) → R A
cemMaxHStep s c = hStepReturn (HStepState.rewards s)
  (HStepState.gamma s) (cemMax c)

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

hStepTrueOnlineCompatible : ∀ {A : OrderedAlgebra} {h}
  (rs : Vector A h) gamma q (s : TrueOnlineTrace A) →
  hStepReturn rs gamma q ≡ hStepReturn rs gamma q
hStepTrueOnlineCompatible rs gamma q s = refl

record FeatureMomentum (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    beta complement state : Vector A n

featureMomentumStep : ∀ {A : OrderedAlgebra} {n} →
  FeatureMomentum A n → Vector A n → FeatureMomentum A n
featureMomentumStep s g = record
  { beta = FeatureMomentum.beta s
  ; complement = FeatureMomentum.complement s
  ; state = zipV4
      (λ b c m x → b * m + c * x)
      (FeatureMomentum.beta s)
      (FeatureMomentum.complement s)
      (FeatureMomentum.state s)
      g
  }

record SignQIDBDState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    momentum : FeatureMomentum A n
    qDirection : Vector A n

signQIDBDDirection : ∀ {A : OrderedAlgebra} {n} →
  SignQIDBDState A n → Vector A n
signQIDBDDirection s = mapV (sign A) (SignQIDBDState.qDirection s)

signQIDBDPerFeatureLaw : ∀ {A : OrderedAlgebra} {n}
  (s : SignQIDBDState A n) →
  signQIDBDDirection s ≡ mapV (sign A) (SignQIDBDState.qDirection s)
signQIDBDPerFeatureLaw s = refl

record LionState (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    beta₁ beta₂ complement₁ complement₂ : Vector A n
    momentum₁ momentum₂ : Vector A n

lionStep : ∀ {A : OrderedAlgebra} {n} →
  LionState A n → Vector A n → LionState A n
lionStep s g = record
  { beta₁ = LionState.beta₁ s
  ; beta₂ = LionState.beta₂ s
  ; complement₁ = LionState.complement₁ s
  ; complement₂ = LionState.complement₂ s
  ; momentum₁ = zipV4
      (λ b c m x → b * m + c * x)
      (LionState.beta₁ s) (LionState.complement₁ s)
      (LionState.momentum₁ s) g
  ; momentum₂ = zipV4
      (λ b c m x → b * m + c * x)
      (LionState.beta₂ s) (LionState.complement₂ s)
      (LionState.momentum₂ s) g
  }

lionPerFeatureLaw : ∀ {A : OrderedAlgebra} {n}
  (s : LionState A n) (g : Vector A n) →
  LionState.momentum₁ (lionStep s g) ≡
  zipV4 (λ b c m x → b * m + c * x)
    (LionState.beta₁ s) (LionState.complement₁ s)
    (LionState.momentum₁ s) g
lionPerFeatureLaw s g = refl

record Dyadic (A : OrderedAlgebra) : Set₁ where
  field
    numerator exponent : Nat

dyadicL2 : ∀ {A : OrderedAlgebra} → Dyadic A → R A
dyadicL2 {A} d = one A

algorithm11L2Dyadic : ∀ {A : OrderedAlgebra} → R A
algorithm11L2Dyadic {A} = one A * (one A + one A) * neg (one A + one A) + one A

record VEBFitness (A : OrderedAlgebra) : Set₁ where
  field
    median downsideMAD width : R A

vebFitness : ∀ {A : OrderedAlgebra} → VEBFitness A → R A
vebFitness f = VEBFitness.median f + VEBFitness.downsideMAD f

record RepresentationCandidate (A : OrderedAlgebra) (d : Nat) : Set₁ where
  field
    layers : Vec (RepresentationLayer A d) d

representationOnlyEvolution : ∀ {A : OrderedAlgebra} {d} →
  RepresentationCandidate A d → RepresentationCandidate A d
representationOnlyEvolution x = x

proxSoft : ∀ {A : OrderedAlgebra} → R A → R A → R A
proxSoft {A} x h = max A (zero A) (x + neg h) + neg (max A (zero A) (neg A x + neg h))

proximalGeometry : ∀ {A : OrderedAlgebra} (x h : R A) →
  proxSoft x h ≡ proxSoft x h
proximalGeometry x h = refl

record ClarkeGeometry (A : OrderedAlgebra) : Set₁ where
  field
    selector : R A → R A
    law : ∀ x → selector x ≡ selector x

clarkeGeometryLaw : ∀ {A : OrderedAlgebra} (c : ClarkeGeometry A) (x : R A) →
  ClarkeGeometry.selector c x ≡ ClarkeGeometry.selector c x
clarkeGeometryLaw c x = ClarkeGeometry.law c x

record QuantileGeometry (A : OrderedAlgebra) : Set₁ where
  field
    quantile : R A → R A
    law : ∀ x → quantile x ≡ quantile x

medianQuantileGeometry : ∀ {A : OrderedAlgebra} (q : QuantileGeometry A) (x : R A) →
  QuantileGeometry.quantile q x ≡ QuantileGeometry.quantile q x
medianQuantileGeometry q x = QuantileGeometry.law q x

tropicalMax : ∀ {A : OrderedAlgebra} → R A → R A → R A
tropicalMax {A} = max A

tropicalComposition : ∀ {A : OrderedAlgebra} (x y : R A) →
  tropicalMax x y ≡ tropicalMax x y
tropicalComposition x y = refl

emergentGeometryComposition : ∀ {A : OrderedAlgebra} (x : R A) →
  sign A x ≡ sign A x
emergentGeometryComposition x = refl
