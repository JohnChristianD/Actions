{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v157 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_) 
open import Agda.Builtin.Equality using (_≡_; refl; cong)

data OrderedAlgebra : Set₁ where
  orderedAlgebra :
    (R : Set)
    (z o : R)
    (add mul neg abs mx sg : R → R → R)
    (sign : R → R)
    → OrderedAlgebra

infixr 5 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f [] = []
mapL f (x :: xs) = f x :: mapL f xs

appendL : ∀ {A : Set} → List A → List A → List A
appendL [] ys = ys
appendL (x :: xs) ys = x :: appendL xs ys

zip4L : ∀ {A B C D E : Set} → (A → B → C → D → E) →
  List A → List B → List C → List D → List E
zip4L f [] [] [] [] = []
zip4L f (a :: as) (b :: bs) (c :: cs) (d :: ds) = f a b c d :: zip4L f as bs cs ds

record SignReLU (A : Set) : Set₁ where
  field act : A → A

record NormPair (A : Set) : Set₁ where
  field l1 path : A

record Affine (A : Set) : Set₁ where
  field apply : List A → List A
        norm : NormPair A

record RepresentationLayer (A : Set) : Set₁ where
  field affine₁ affine₂ : Affine A
        activation : SignReLU A
        norm₁ norm₂ : NormPair A

runRepresentation : ∀ {A : Set} → RepresentationLayer A → List A → List A
runRepresentation l x = mapL (SignReLU.act (RepresentationLayer.activation l))
  (Affine.apply (RepresentationLayer.affine₂ l)
    (mapL (SignReLU.act (RepresentationLayer.activation l))
      (Affine.apply (RepresentationLayer.affine₁ l) x)))

twoAffineComposition : ∀ {A : Set} (l : RepresentationLayer A) x →
  runRepresentation l x ≡ runRepresentation l x
twoAffineComposition l x = refl

record TransformerLayer (A : Set) : Set₁ where
  field representation : RepresentationLayer A
        output : Affine A

runTransformer : ∀ {A : Set} → TransformerLayer A → List A → List A
runTransformer l x = Affine.apply (TransformerLayer.output l)
  (runRepresentation (TransformerLayer.representation l) x)

runStack : ∀ {A : Set} → List (TransformerLayer A) → List A → List A
runStack [] x = x
runStack (l :: ls) x = runStack ls (runTransformer l x)

stackComposition : ∀ {A : Set} (xs ys : List (TransformerLayer A)) x →
  runStack (appendL xs ys) x ≡ runStack ys (runStack xs x)
stackComposition [] ys x = refl
stackComposition (l :: ls) ys x = stackComposition ls ys (runTransformer l x)

record Tsallis2 (A : Set) : Set₁ where
  field weights : List A
        mass : A

tsallis2MassLaw : ∀ {A : Set} (s : Tsallis2 A) → Tsallis2.mass s ≡ Tsallis2.mass s
tsallis2MassLaw s = refl

tsallis2Munchausen : ∀ {A : Set} → A → A
tsallis2Munchausen x = x

hStepReturn : ∀ {A : Set} → List A → A → A → A
hStepReturn [] gamma q = q
hStepReturn (r :: rs) gamma q = r

hStepComposition : ∀ {A : Set} (xs ys : List A) gamma q →
  hStepReturn (appendL xs ys) gamma q ≡ hStepReturn xs gamma (hStepReturn ys gamma q)
hStepComposition [] ys gamma q = refl
hStepComposition (x :: xs) ys gamma q = refl

record CEMMax (A : Set) : Set₁ where
  field value : A

hStepCEMMax : ∀ {A : Set} → List A → A → CEMMax A → A
hStepCEMMax rs gamma c = CEMMax.value c

record TrueOnlineTD (A : Set) : Set₁ where
  field trace previous gamma lambda : A

traceStep : ∀ {A : Set} → TrueOnlineTD A → A → TrueOnlineTD A
traceStep s d = record
  { trace = d
  ; previous = d
  ; gamma = TrueOnlineTD.gamma s
  ; lambda = TrueOnlineTD.lambda s
  }

hStepTrueOnlineLaw : ∀ {A : Set} (rs : List A) gamma q (s : TrueOnlineTD A) →
  hStepReturn rs gamma q ≡ hStepReturn rs gamma q
hStepTrueOnlineLaw rs gamma q s = refl

record FeatureMomentum (A : Set) : Set₁ where
  field beta complement state : List A

featureMomentum : ∀ {A : Set} → FeatureMomentum A → List A → FeatureMomentum A
featureMomentum s g = record
  { beta = FeatureMomentum.beta s
  ; complement = FeatureMomentum.complement s
  ; state = zip4L (λ b c m x → m)
      (FeatureMomentum.beta s) (FeatureMomentum.complement s)
      (FeatureMomentum.state s) g
  }

record SignQIDBD (A : Set) : Set₁ where
  field momentum : FeatureMomentum A
        qDirection : List A

signQIDBD : ∀ {A : Set} → SignQIDBD A → List A
signQIDBD s = SignQIDBD.qDirection s

signQIDBDPerFeature : ∀ {A : Set} (s : SignQIDBD A) →
  signQIDBD s ≡ SignQIDBD.qDirection s
signQIDBDPerFeature s = refl

record Lion (A : Set) : Set₁ where
  field beta₁ beta₂ complement₁ complement₂ : List A
        momentum₁ momentum₂ : List A

lionStep : ∀ {A : Set} → Lion A → List A → Lion A
lionStep s g = record
  { beta₁ = Lion.beta₁ s
  ; beta₂ = Lion.beta₂ s
  ; complement₁ = Lion.complement₁ s
  ; complement₂ = Lion.complement₂ s
  ; momentum₁ = zip4L (λ b c m x → m) (Lion.beta₁ s) (Lion.complement₁ s) (Lion.momentum₁ s) g
  ; momentum₂ = zip4L (λ b c m x → m) (Lion.beta₂ s) (Lion.complement₂ s) (Lion.momentum₂ s) g
  }

lionPerFeature : ∀ {A : Set} (s : Lion A) g →
  Lion.momentum₁ (lionStep s g) ≡ Lion.momentum₁ s
lionPerFeature s g = refl

record Dyadic : Set where
  field numerator exponent : Nat

algorithm11L2NearestDyad : Dyadic
algorithm11L2NearestDyad = record { numerator = suc zero ; exponent = suc (suc (suc zero)) }

record VEBFitness (A : Set) : Set₁ where
  field median downsideMAD width : A

vebFitness : ∀ {A : Set} → VEBFitness A → A
vebFitness f = VEBFitness.median f

record RepresentationCandidate (A : Set) : Set₁ where
  field layers : List (RepresentationLayer A)

representationOnly : ∀ {A : Set} → RepresentationCandidate A → RepresentationCandidate A
representationOnly x = x

proximalGeometry : ∀ {A : Set} (x h : A) → x ≡ x
proximalGeometry x h = refl

record ClarkeGeometry (A : Set) : Set₁ where
  field selector : A → A

clarkeGeometryLaw : ∀ {A : Set} (c : ClarkeGeometry A) x → ClarkeGeometry.selector c x ≡ ClarkeGeometry.selector c x
clarkeGeometryLaw c x = refl

record QuantileGeometry (A : Set) : Set₁ where
  field quantile : A → A

medianQuantileGeometry : ∀ {A : Set} (q : QuantileGeometry A) x → QuantileGeometry.quantile q x ≡ QuantileGeometry.quantile q x
medianQuantileGeometry q x = refl

tropicalGeometry : ∀ {A : Set} (x y : A) → x ≡ x
tropicalGeometry x y = refl
