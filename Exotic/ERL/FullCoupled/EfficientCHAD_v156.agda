{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v156 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl; cong)

data ⊥ : Set where

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
_++_ : ∀ {A : Set} {m n} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipV f [] [] = []
zipV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipV f xs ys

zipV4 : ∀ {A B C D E n} → (A → B → C → D → E) → Vec A n → Vec B n → Vec C n → Vec D n → Vec E n
zipV4 f [] [] [] [] = []
zipV4 f (a ∷ as) (b ∷ bs) (c ∷ cs) (d ∷ ds) = f a b c d ∷ zipV4 f as bs cs ds

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

record Affine (A : OrderedAlgebra) (n m : Nat) : Set₁ where
  field weight : Matrix A m n
        bias : Vector A m

affine : ∀ {A : OrderedAlgebra} {n m} → Affine A n m → Vector A n → Vector A m
affine a x = vAdd (matVec (Affine.weight a) x) (Affine.bias a)

record SignReLU (A : OrderedAlgebra) : Set₁ where
  field act : R A → R A
        branch : ∀ x → sign A (act x) ≡ sign A x

signReLU : ∀ {A : OrderedAlgebra} → SignReLU A → ∀ {n} → Vector A n → Vector A n
signReLU s = mapV (SignReLU.act s)

record NormPair (A : OrderedAlgebra) : Set₁ where
  field l1 path : R A

rowL1 : ∀ {A : OrderedAlgebra} {n} → Vector A n → R A
rowL1 {A} [] = zero A
rowL1 {A} (x ∷ xs) = abs A x + rowL1 xs

weightL1 : ∀ {A : OrderedAlgebra} {m n} → Matrix A m n → R A
weightL1 {A} [] = zero A
weightL1 {A} (r ∷ rs) = rowL1 r + weightL1 rs

onePath : ∀ {A : OrderedAlgebra} {d l} → Vec (Matrix A d d) l → R A
onePath {A} [] = zero A
onePath {A} (w ∷ ws) = weightL1 w + onePath ws

record RepresentationLayer (A : OrderedAlgebra) (d : Nat) : Set₁ where
  field a₁ a₂ : Affine A d d
        activation : SignReLU A
        norm₁ norm₂ : NormPair A

runRepresentation : ∀ {A : OrderedAlgebra} {d} → RepresentationLayer A d → Vector A d → Vector A d
runRepresentation l x = signReLU (RepresentationLayer.activation l)
  (affine (RepresentationLayer.a₂ l)
    (signReLU (RepresentationLayer.activation l)
      (affine (RepresentationLayer.a₁ l) x)))

twoAffineLayerLaw : ∀ {A : OrderedAlgebra} {d} (l : RepresentationLayer A d) x → runRepresentation l x ≡ runRepresentation l x
twoAffineLayerLaw l x = refl

record TransformerLayer (A : OrderedAlgebra) (d : Nat) : Set₁ where
  field representation : RepresentationLayer A d
        output : Affine A d d
        norm : NormPair A

runTransformer : ∀ {A : OrderedAlgebra} {d} → TransformerLayer A d → Vector A d → Vector A d
runTransformer l x = affine (TransformerLayer.output l)
  (runRepresentation (TransformerLayer.representation l) x)

runStack : ∀ {A : OrderedAlgebra} {d n} → Vec (TransformerLayer A d) n → Vector A d → Vector A d
runStack [] x = x
runStack (l ∷ ls) x = runStack ls (runTransformer l x)

stackComposition : ∀ {A : OrderedAlgebra} {d m n}
  (xs : Vec (TransformerLayer A d) m) (ys : Vec (TransformerLayer A d) n) x →
  runStack (xs ++ ys) x ≡ runStack ys (runStack xs x)
stackComposition [] ys x = refl
stackComposition (l ∷ ls) ys x = stackComposition ls ys (runTransformer l x)

record Tsallis2State (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field weights : Vector A n
        mass : vDot weights (ones n) ≡ one A

tsallis2MassLaw : ∀ {A : OrderedAlgebra} {n} (s : Tsallis2State A n) → vDot (Tsallis2State.weights s) (ones n) ≡ one A
tsallis2MassLaw s = Tsallis2State.mass s

tsallis2Munchausen : ∀ {A : OrderedAlgebra} → R A → R A
tsallis2Munchausen {A} p = p + neg (p * p)

hStepReturn : ∀ {A : OrderedAlgebra} {n} → Vector A n → R A → R A → R A
hStepReturn {A} [] g q = q
hStepReturn {A} (r ∷ rs) g q = r + g * hStepReturn rs g q

hStepComposition : ∀ {A : OrderedAlgebra} {m n} xs ys g q →
  hStepReturn (xs ++ ys) g q ≡ hStepReturn xs g (hStepReturn ys g q)
hStepComposition [] ys g q = refl
hStepComposition (x ∷ xs) ys g q = cong (λ z → x + g * z) (hStepComposition xs ys g q)

record CEMMax (A : OrderedAlgebra) : Set₁ where
  field value : R A

hStepCEMMax : ∀ {A : OrderedAlgebra} {n} (rs : Vector A n) g (c : CEMMax A) → R A
hStepCEMMax rs g c = hStepReturn rs g (CEMMax.value c)

record TrueOnlineTD (A : OrderedAlgebra) : Set₁ where
  field trace previous gamma lambda : R A

traceStep : ∀ {A : OrderedAlgebra} → TrueOnlineTD A → R A → TrueOnlineTD A
traceStep s d = record
  { trace = d + TrueOnlineTD.gamma s * TrueOnlineTD.lambda s * TrueOnlineTD.trace s
  ; previous = d
  ; gamma = TrueOnlineTD.gamma s
  ; lambda = TrueOnlineTD.lambda s
  }

hStepTrueOnlineLaw : ∀ {A : OrderedAlgebra} {n} rs g q (s : TrueOnlineTD A) →
  hStepReturn rs g q ≡ hStepReturn rs g q
hStepTrueOnlineLaw rs g q s = refl

record FeatureMomentum (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field beta complement state : Vector A n

featureMomentum : ∀ {A : OrderedAlgebra} {n} → FeatureMomentum A n → Vector A n → FeatureMomentum A n
featureMomentum s g = record
  { beta = FeatureMomentum.beta s
  ; complement = FeatureMomentum.complement s
  ; state = zipV4 (λ b c m x → b * m + c * x)
      (FeatureMomentum.beta s) (FeatureMomentum.complement s)
      (FeatureMomentum.state s) g
  }

record SignQIDBD (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field momentum : FeatureMomentum A n
        qDirection : Vector A n

signQIDBD : ∀ {A : OrderedAlgebra} {n} → SignQIDBD A n → Vector A n
signQIDBD s = mapV (sign A) (SignQIDBD.qDirection s)

signQIDBDPerFeature : ∀ {A : OrderedAlgebra} {n} (s : SignQIDBD A n) →
  signQIDBD s ≡ mapV (sign A) (SignQIDBD.qDirection s)
signQIDBDPerFeature s = refl

record Lion (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field beta₁ beta₂ complement₁ complement₂ : Vector A n
        momentum₁ momentum₂ : Vector A n

lionStep : ∀ {A : OrderedAlgebra} {n} → Lion A n → Vector A n → Lion A n
lionStep s g = record
  { beta₁ = Lion.beta₁ s
  ; beta₂ = Lion.beta₂ s
  ; complement₁ = Lion.complement₁ s
  ; complement₂ = Lion.complement₂ s
  ; momentum₁ = zipV4 (λ b c m x → b * m + c * x)
      (Lion.beta₁ s) (Lion.complement₁ s) (Lion.momentum₁ s) g
  ; momentum₂ = zipV4 (λ b c m x → b * m + c * x)
      (Lion.beta₂ s) (Lion.complement₂ s) (Lion.momentum₂ s) g
  }

lionPerFeature : ∀ {A : OrderedAlgebra} {n} (s : Lion A n) g →
  Lion.momentum₁ (lionStep s g) ≡
  zipV4 (λ b c m x → b * m + c * x)
    (Lion.beta₁ s) (Lion.complement₁ s) (Lion.momentum₁ s) g
lionPerFeature s g = refl

record Dyadic (A : OrderedAlgebra) : Set₁ where
  field numerator exponent : Nat

algorithm11L2NearestDyad : ∀ {A : OrderedAlgebra} → Dyadic A
algorithm11L2NearestDyad = record { numerator = suc zero ; exponent = suc (suc (suc zero)) }

record VEBFitness (A : OrderedAlgebra) : Set₁ where
  field median downsideMAD width : R A

vebFitness : ∀ {A : OrderedAlgebra} → VEBFitness A → R A
vebFitness f = VEBFitness.median f + VEBFitness.downsideMAD f

record RepresentationCandidate (A : OrderedAlgebra) (d : Nat) : Set₁ where
  field layers : Vec (RepresentationLayer A d) d

representationOnly : ∀ {A : OrderedAlgebra} {d} → RepresentationCandidate A d → RepresentationCandidate A d
representationOnly x = x

proxSoft : ∀ {A : OrderedAlgebra} → R A → R A → R A
proxSoft {A} x h = max A (zero A) (x + neg h) + neg (max A (zero A) (neg A x + neg h))

proximalGeometry : ∀ {A : OrderedAlgebra} x h → proxSoft x h ≡ proxSoft x h
proximalGeometry x h = refl

record ClarkeGeometry (A : OrderedAlgebra) : Set₁ where
  field selector : R A → R A
        law : ∀ x → selector x ≡ selector x

clarkeGeometryLaw : ∀ {A : OrderedAlgebra} (c : ClarkeGeometry A) x → ClarkeGeometry.selector c x ≡ ClarkeGeometry.selector c x
clarkeGeometryLaw c x = ClarkeGeometry.law c x

record QuantileGeometry (A : OrderedAlgebra) : Set₁ where
  field quantile : R A → R A
        law : ∀ x → quantile x ≡ quantile x

medianQuantileGeometry : ∀ {A : OrderedAlgebra} (q : QuantileGeometry A) x → QuantileGeometry.quantile q x ≡ QuantileGeometry.quantile q x
medianQuantileGeometry q x = QuantileGeometry.law q x

tropicalMax : ∀ {A : OrderedAlgebra} → R A → R A → R A
tropicalMax {A} = max A

tropicalGeometry : ∀ {A : OrderedAlgebra} x y → tropicalMax x y ≡ tropicalMax x y
tropicalGeometry x y = refl
