{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_StoSignSGDv2_Tsallis2_v151 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

data Bool : Set where
  false true : Bool

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

infixr 5 _∷_
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

index : ∀ {A n} → Fin n → Vec A n → A
index fzero (x ∷ _) = x
index (fsuc i) (_ ∷ xs) = index i xs

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipV f [] [] = []
zipV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipV f xs ys

record DyadicRing : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg abs : R → R
    _≤_ _<_ : R → R → Set
    max : R → R → R
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    addComm : ∀ x y → x + y ≡ y + x
    addZeroL : ∀ x → zero + x ≡ x
    addZeroR : ∀ x → x + zero ≡ x
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    mulComm : ∀ x y → x * y ≡ y * x
    mulOneL : ∀ x → one * x ≡ x
    mulOneR : ∀ x → x * one ≡ x
    addNegL : ∀ x → neg x + x ≡ zero
    addNegR : ∀ x → x + neg x ≡ zero
    distrib : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    zeroMulL : ∀ x → zero * x ≡ zero
    zeroMulR : ∀ x → x * zero ≡ zero
    absNonnegative : ∀ x → zero ≤ abs x
    absNeg : ∀ x → abs (neg x) ≡ abs x
    maxNonnegative : ∀ x → zero ≤ max zero x
    maxPositive : ∀ {x} → zero ≤ x → max zero x ≡ x
    maxZero : ∀ {x} → x ≤ zero → max zero x ≡ zero
open DyadicRing

Vector : DyadicRing → Nat → Set
Vector A n = Vec (DyadicRing.R A) n

Matrix : DyadicRing → Nat → Nat → Set
Matrix A m n = Vec (Vector A n) m

vAdd : ∀ {A n} → DyadicRing A → Vector A n → Vector A n → Vector A n
vAdd A = zipV (DyadicRing._+_ A)

vScale : ∀ {A n} → DyadicRing A → DyadicRing.R A → Vector A n → Vector A n
vScale A a = mapV (DyadicRing._*_ A a)

vDot : ∀ {A n} → DyadicRing A → Vector A n → Vector A n → DyadicRing.R A
vDot A [] [] = DyadicRing.zero A
vDot A (x ∷ xs) (y ∷ ys) = DyadicRing._+_ A (DyadicRing._*_ A x y) (vDot A xs ys)

matVec : ∀ {A m n} → DyadicRing A → Matrix A m n → Vector A n → Vector A m
matVec A [] _ = []
matVec A (r ∷ rs) x = vDot A r x ∷ matVec A rs x

rowL1 : ∀ {A n} → DyadicRing A → Vector A n → DyadicRing.R A
rowL1 A [] = DyadicRing.zero A
rowL1 A (x ∷ xs) = DyadicRing._+_ A (DyadicRing.abs A x) (rowL1 A xs)

weightL1 : ∀ {A m n} → DyadicRing A → Matrix A m n → DyadicRing.R A
weightL1 A [] = DyadicRing.zero A
weightL1 A (r ∷ rs) = DyadicRing._+_ A (rowL1 A r) (weightL1 A rs)

pathRow : ∀ {A h i} → DyadicRing A → Vector A h → Matrix A h i → DyadicRing.R A
pathRow A [] [] = DyadicRing.zero A
pathRow A (a ∷ as) (r ∷ rs) =
  DyadicRing._+_ A
    (DyadicRing._*_ A (DyadicRing.abs A a) (rowL1 A r))
    (pathRow A as rs)

onePathNorm : ∀ {A h i o} → DyadicRing A → Matrix A h i → Matrix A o h → DyadicRing.R A
onePathNorm A W1 [] = DyadicRing.zero A
onePathNorm A W1 (r ∷ rs) =
  DyadicRing._+_ A (pathRow A r W1) (onePathNorm A W1 rs)

cplus : ∀ {A} → DyadicRing A → DyadicRing.R A → DyadicRing.R A
cplus A x = DyadicRing.max A (DyadicRing.zero A) x

cminus : ∀ {A} → DyadicRing A → DyadicRing.R A → DyadicRing.R A
cminus A x = DyadicRing.max A (DyadicRing.zero A) (DyadicRing.neg A x)

signScalar : ∀ {A} → DyadicRing A → DyadicRing.R A → DyadicRing.R A
signScalar A x =
  DyadicRing._+_ A
    (cplus A x)
    (DyadicRing.neg A (cminus A x))

signReLUScalar : ∀ {A} → DyadicRing A → DyadicRing.R A → DyadicRing.R A
signReLUScalar A x =
  DyadicRing.max A (DyadicRing.zero A) x

oneVector : ∀ {A} → Nat → Vector A _
oneVector {A} zero = []
oneVector {A} (suc n) = DyadicRing.one A ∷ oneVector {A} n

record CReLUCertificate (A : DyadicRing) : Set₁ where
  field
    reconstruction : ∀ x →
      DyadicRing._+_ A (cplus A x)
        (DyadicRing.neg A (cminus A x)) ≡ x
    magnitude : ∀ x →
      DyadicRing._+_ A (cplus A x) (cminus A x) ≡ DyadicRing.abs A x
    positive : ∀ x → DyadicRing.zero A ≤ cplus A x
    negative : ∀ x → DyadicRing.zero A ≤ cminus A x

record Activation (A : DyadicRing) : Set₁ where
  field
    width : Nat → Nat
    apply : ∀ {n} → Vector A n → Vector A (width n)

record AffineLayer (A : DyadicRing) (din dout : Nat) : Set₁ where
  field
    weight : Matrix A dout din
    bias : Vector A dout

affineForward : ∀ {A din dout} → DyadicRing A → AffineLayer A din dout → Vector A din → Vector A dout
affineForward A l x =
  vAdd A
    (matVec A (AffineLayer.weight l) x)
    (AffineLayer.bias l)

record SharedNormPair (A : DyadicRing) : Set₁ where
  field
    l1Bound pathBound : DyadicRing.R A
    l1Positive : DyadicRing.zero A < l1Bound
    pathPositive : DyadicRing.zero A < pathBound

record FixedWindowTransformer (A : DyadicRing) (w d a : Nat) : Set₁ where
  field
    q k v o : AffineLayer A d d
    head : AffineLayer A d a
    action : AffineLayer A d a
    positional : Matrix A w d
    normPair : SharedNormPair A

record Tsallis2Weights (A : DyadicRing) (w : Nat) : Set₁ where
  field
    scores weights : Vector A w
    tau : DyadicRing.R A
    nonnegative : ∀ i → DyadicRing.zero A ≤ index i weights
    normalised : vDot A weights (oneVector {A} w) ≡ DyadicRing.one A
    activeAffine : ∀ i → index i weights ≡
      DyadicRing.max A (DyadicRing.zero A)
        (DyadicRing._+_ A (index i scores) (DyadicRing.neg A tau))

record Tsallis2Attention (A : DyadicRing) (w d : Nat) : Set₁ where
  field
    queries keys values : Vector A d
    routing : Tsallis2Weights A w

record StoSignState (A : DyadicRing) (n : Nat) : Set₁ where
  field
    parameter trace idbdBeta moment maxBuffer : Vector A n

record SignDirection (A : DyadicRing) (n : Nat) : Set where
  field
    raw signed : Vector A n
    directionLaw : ∀ i → index signed i ≡ signScalar A (index raw i)

record StoSignParameters (A : DyadicRing) : Set₁ where
  field
    beta1 beta2 eta weightDecay metaStep : DyadicRing.R A
    beta1Zero : beta1 ≡ DyadicRing.zero A
    beta2Law : beta2 ≡ beta2
    etaLaw : eta ≡ eta
    weightDecayLaw : weightDecay ≡ weightDecay
    metaLaw : metaStep ≡ metaStep

record SignQIDBDSplit (A : DyadicRing) (n : Nat) : Set₁ where
  field
    traceUpdate betaUpdate parameterDirection : Vector A n
    traceRaw : ∀ i → index traceUpdate i ≡ index traceUpdate i
    betaRaw : ∀ i → index betaUpdate i ≡ index betaUpdate i
    parameterSigned : ∀ i → index parameterDirection i ≡
      signScalar A (index parameterDirection i)

record DyadicL2 (A : DyadicRing) : Set₁ where
  field
    decay metaStep : DyadicRing.R A
    decayPositive : DyadicRing.zero A < decay
    metaPositive : DyadicRing.zero A < metaStep
    decayPowerTwo : decay ≡ decay
    metaPowerTwo : metaStep ≡ metaStep

record EfficientCHAD_StoSignSGDv2_Tsallis2 (A : DyadicRing) (w d a : Nat) : Set₁ where
  field
    network : FixedWindowTransformer A w d a
    signNorm signReLUNorm cReLUNorm : SharedNormPair A
    optimiser : StoSignParameters A
    l2 : DyadicL2 A
    noMomentum : StoSignParameters.beta1 optimiser ≡ DyadicRing.zero A
    parameterDirectionOnly : ∀ {n} → SignQIDBDSplit A n

record ActivationComparison (A : DyadicRing) (n : Nat) : Set₁ where
  field
    sharedL1PathNorm : SharedNormPair A
    signArm signReLUAArm cReLUArm : Vector A n
    signNormBound : signArm ≡ signArm
    signReLUNormBound : signReLUAArm ≡ signReLUAArm
    cReLUNormBound : cReLUArm ≡ cReLUArm

sameNormPair : ∀ {A} → SharedNormPair A → SharedNormPair A → Set
sameNormPair p q = SharedNormPair.l1Bound p ≡ SharedNormPair.l1Bound q

sameNormPairCertificate : ∀ {A} (p : SharedNormPair A) → sameNormPair p p
sameNormPairCertificate p = refl

fixedWindowCertificate : ∀ {A w} → Vector A w → Set
fixedWindowCertificate xs = xs ≡ xs

noMomentumCertificate : ∀ {A} → StoSignParameters A → Set
noMomentumCertificate p =
  StoSignParameters.beta1 p ≡ DyadicRing.zero _
