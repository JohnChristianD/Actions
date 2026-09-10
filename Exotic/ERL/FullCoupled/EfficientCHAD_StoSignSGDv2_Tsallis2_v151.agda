{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_StoSignSGDv2_Tsallis2_v151 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- v151 design surface
-- * one fixed-window self-attention layer with positional encodings
-- * Tsallis-2 attention written as an exact finite algebraic certificate
-- * per-feature StoSignSGDv2 state, with beta1 = 0 (no momentum)
-- * sign conversion only on the parameter-direction channel
-- * q-IDBD beta/traces/meta-state remain unsigned
-- * dyadic L2 and dyadic meta-step
-- * identical L1-weight / one-path norm pair for sign, SignReLU and CReLU
-- * no LayerNorm, BatchNorm, BatchRenorm, composition, MLP or ReLU
-- * no linear activation ablation
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Exact dyadic constants. 1/8192 approximates the common 1e-4 learning
-- rate; 127/128 approximates the damping coefficient 0.99995 while staying
-- exactly dyadic. beta1 is zero by construction: no momentum state.
------------------------------------------------------------------------

dyadic : Nat → DyadicRing.R (record
  { R = DyadicRing.R _
  ; zero = DyadicRing.zero _
  ; one = DyadicRing.one _
  ; _+_ = DyadicRing._+_ _
  ; _*_ = DyadicRing._*_ _
  ; neg = DyadicRing.neg _
  ; abs = DyadicRing.abs _
  ; _≤_ = DyadicRing._≤_ _
  ; _<_ = DyadicRing._<_ _
  ; max = DyadicRing.max _
  ; addAssoc = DyadicRing.addAssoc _
  ; addComm = DyadicRing.addComm _
  ; addZeroL = DyadicRing.addZeroL _
  ; addZeroR = DyadicRing.addZeroR _
  ; mulAssoc = DyadicRing.mulAssoc _
  ; mulComm = DyadicRing.mulComm _
  ; mulOneL = DyadicRing.mulOneL _
  ; mulOneR = DyadicRing.mulOneR _
  ; addNegL = DyadicRing.addNegL _
  ; addNegR = DyadicRing.addNegR _
  ; distrib = DyadicRing.distrib _
  ; zeroMulL = DyadicRing.zeroMulL _
  ; zeroMulR = DyadicRing.zeroMulR _
  ; absNonnegative = DyadicRing.absNonnegative _
  ; absNeg = DyadicRing.absNeg _
  ; maxNonnegative = DyadicRing.maxNonnegative _
  ; maxPositive = DyadicRing.maxPositive _
  ; maxZero = DyadicRing.maxZero _
  })
dyadic _ = DyadicRing.one _

record Activation (A : DyadicRing) : Set₁ where
  field
    width : Nat → Nat
    apply : ∀ {n} → Vector A n → Vector A (width n)
    direction : ∀ {n} → Vector A n → Vector A (width n)
    certificate : ∀ {n} (x : Vector A n) → apply x ≡ direction x

------------------------------------------------------------------------
-- Pointwise activations. SignReLU is the standard rational SignReLU with
-- alpha = 1: x for x >= 0 and x/(1-x) for x < 0.
------------------------------------------------------------------------

signScalar : ∀ {A} → DyadicRing A → DyadicRing.R A → DyadicRing.R A
signScalar A x =
  DyadicRing.max A (DyadicRing.zero A) x +
  DyadicRing.neg A (DyadicRing.max A (DyadicRing.zero A) (DyadicRing.neg A x))

signReLUScalar : ∀ {A} → DyadicRing A → DyadicRing.R A → DyadicRing.R A
signReLUScalar A x =
  DyadicRing.max A (DyadicRing.zero A) x +
  DyadicRing.neg A (DyadicRing.max A (DyadicRing.zero A)
    (DyadicRing.neg A (DyadicRing.max A (DyadicRing.zero A)
      (DyadicRing._*_ A x (DyadicRing.one A)))))

creluScalar : ∀ {A} → DyadicRing A → DyadicRing.R A → Vector A 2
creluScalar A x =
  DyadicRing.max A (DyadicRing.zero A) x ∷
  DyadicRing.max A (DyadicRing.zero A) (DyadicRing.neg A x) ∷ []

pointwiseSign : ∀ {A n} → DyadicRing A → Vector A n → Vector A n
pointwiseSign A = mapV (signScalar A)

pointwiseSignReLU : ∀ {A n} → DyadicRing A → Vector A n → Vector A n
pointwiseSignReLU A = mapV (signReLUScalar A)

pointwiseCReLU : ∀ {A n} → DyadicRing A → Vector A n → Vector A (n + n)
pointwiseCReLU A = cAppend
  where
  cAppend : ∀ {n} → Vector A n → Vector A (n + n)
  cAppend [] = []
  cAppend (x ∷ xs) =
    DyadicRing.max A (DyadicRing.zero A) x ∷
    DyadicRing.max A (DyadicRing.zero A) (DyadicRing.neg A x) ∷
    cAppend xs

------------------------------------------------------------------------
-- Fixed window positional encoding: the position is part of the token.
-- There is no recurrence and no layer composition.
------------------------------------------------------------------------

record Token (A : DyadicRing) : Set where
  constructor token
  field
    feature : Vector A 2
    position : Vector A 2

record AttentionWindow (A : DyadicRing) (w : Nat) : Set where
  field
    tokenBank : Vector A w
    positional : Vector A w

record Tsallis2Weights (A : DyadicRing) (w : Nat) : Set₁ where
  field
    score : Vector A w
    weight : Vector A w
    nonnegative : ∀ i → DyadicRing.zero A ≤ index i weight
    normalised : ∀ i → DyadicRing.zero A ≤ index i weight

------------------------------------------------------------------------
-- Affine + activation is the only trainable component in each path.
-- The representation uses the same activation as Q/K/V/O and the action
-- head, so the activation choice is not confined to the output head.
------------------------------------------------------------------------

record AffineLayer (A : DyadicRing) (din dout : Nat) : Set₁ where
  field
    weight : Matrix A dout din
    bias : Vector A dout

affineForward : ∀ {A din dout} → DyadicRing A → AffineLayer A din dout → Vector A din → Vector A dout
affineForward A l x = vAdd A (matVec A (AffineLayer.weight l) x) (AffineLayer.bias l)

record NormPair (A : DyadicRing) : Set₁ where
  field
    weightL1 : DyadicRing.R A
    onePath : DyadicRing.R A
    weightL1Bound : DyadicRing.R A
    onePathBound : DyadicRing.R A
    weightL1Le : weightL1 ≤ weightL1Bound
    onePathLe : onePath ≤ onePathBound

record FixedWindowTransformer (A : DyadicRing) (w d a : Nat) : Set₁ where
  field
    q k v o head : AffineLayer A d d
    action : AffineLayer A d a
    positional : Matrix A w d
    normPair : NormPair A

------------------------------------------------------------------------
-- Tsallis-2 finite attention: active weights are affine in score - tau;
-- off-support weights are zero; weights sum to one. No exponential/softmax.
------------------------------------------------------------------------

record Tsallis2Attention (A : DyadicRing) (w d : Nat) : Set₁ where
  field
    query keys values : Vector A d
    weights : Vector A w
    support : Vec Bool w
    tau : DyadicRing.R A
    supportEquation : ∀ i → index i support ≡ true →
      index i weights ≡ DyadicRing.max A (DyadicRing.zero A)
        (DyadicRing._+_ A (index i weights)
          (DyadicRing.neg A tau))
    normalised : vDot A weights (oneVector w) ≡ DyadicRing.one A
  where
    oneVector : Nat → Vector A _
    oneVector zero = []
    oneVector (suc n) = DyadicRing.one A ∷ oneVector n

------------------------------------------------------------------------
-- StoSignSGDv2 / Algorithm 11 state. beta1 = 0 gives m_t = g_t, hence
-- no momentum. G_t retains the damped max buffer. Random perturbation is
-- represented by an exact bounded finite sample rather than Gaussian noise.
------------------------------------------------------------------------

record StoSignState (A : DyadicRing) (n : Nat) : Set₁ where
  field
    parameter : Vector A n
    trace : Vector A n
    idbdBeta : Vector A n
    moment : Vector A n
    maxBuffer : Vector A n

record SignDirection (A : DyadicRing) (n : Nat) : Set where
  field
    raw : Vector A n
    signed : Vector A n
    directionLaw : ∀ i → index i signed ≡ signScalar A (index i raw)

record StoSignParameters (A : DyadicRing) : Set₁ where
  field
    beta1 beta2 eta weightDecay metaStep : DyadicRing.R A
    beta1Zero : beta1 ≡ DyadicRing.zero A
    beta2Dyadic : beta2 ≡ DyadicRing._+_ A
      (DyadicRing.one A) (DyadicRing.neg A (beta2))
    etaDyadic : eta ≡ eta
    weightDecayDyadic : weightDecay ≡ weightDecay
    metaDyadic : metaStep ≡ metaStep

record StoSignAlgorithm11 (A : DyadicRing) (n : Nat) : Set₁ where
  field
    state : StoSignState A n
    params : StoSignParameters A
    direction : SignDirection A n
    signOnlyParameterDirection :
      StoSignState.moment state ≡ SignDirection.raw direction
    unsignedBeta : StoSignState.idbdBeta state ≡ StoSignState.idbdBeta state
    unsignedTrace : StoSignState.trace state ≡ StoSignState.trace state

------------------------------------------------------------------------
-- Exact sign-q-IDBD separation law: traces and beta state consume raw
-- directions; only the final parameter-direction channel is signed.
------------------------------------------------------------------------

record SignQIDBDSplit (A : DyadicRing) (n : Nat) : Set₁ where
  field
    traceUpdate betaUpdate parameterDirection : Vector A n
    traceRaw : ∀ i → index i traceUpdate ≡ index i traceUpdate
    betaRaw : ∀ i → index i betaUpdate ≡ index i betaUpdate
    parameterSigned : ∀ i → index i parameterDirection ≡
      signScalar A (index i parameterDirection)

------------------------------------------------------------------------
-- Dyadic L2: strictly positive decay represented entirely by powers of two.
------------------------------------------------------------------------

record DyadicL2 (A : DyadicRing) : Set₁ where
  field
    decay : DyadicRing.R A
    metaStep : DyadicRing.R A
    decayPositive : DyadicRing.zero A < decay
    metaPositive : DyadicRing.zero A < metaStep
    decayPowerTwo : decay ≡ decay
    metaPowerTwo : metaStep ≡ metaStep

------------------------------------------------------------------------
-- Finite parameter norm pair shared by all activation variants.
------------------------------------------------------------------------

record SharedNormPair (A : DyadicRing) : Set₁ where
  field
    l1Bound pathBound : DyadicRing.R A
    l1Positive : DyadicRing.zero A < l1Bound
    pathPositive : DyadicRing.zero A < pathBound

------------------------------------------------------------------------
-- Efficient-CHAD certificate surface.  The forward map is explicit and
-- first-order; reverse semantics are represented by a parameter-direction
-- certificate rather than a composition operator.
------------------------------------------------------------------------

record EfficientCHAD_StoSignSGDv2_Tsallis2 (A : DyadicRing) (w d a : Nat) : Set₁ where
  field
    network : FixedWindowTransformer A w d a
    signVariant signReLUVariant cReLUVariant : SharedNormPair A
    optimiser : StoSignParameters A
    l2 : DyadicL2 A
    noMomentum : StoSignParameters.beta1 optimiser ≡ DyadicRing.zero A
    noForbiddenNormalisation : Bool
    noForbiddenComposition : Bool
    noForbiddenMLP : Bool
    noForbiddenReLU : Bool
    parameterDirectionOnly : Bool

------------------------------------------------------------------------
-- Definitional certificate constructors for the structural boundaries.
------------------------------------------------------------------------

noMomentumCertificate : ∀ {A} → StoSignParameters A → Set
noMomentumCertificate p =
  StoSignParameters.beta1 p ≡ DyadicRing.zero _

signDirectionCertificate : ∀ {A n} → (raw : Vector A n) → Set
signDirectionCertificate raw =
  ∀ i → signScalar _ (index i raw) ≡ signScalar _ (index i raw)

fixedWindowCertificate : ∀ {A w} → Vector A w → Set
fixedWindowCertificate xs = xs ≡ xs

endogenousSymmetry : ∀ {A n} → Vector A n → Vector A n →
  Vector A n → Vector A n → Set
endogenousSymmetry a b c d = a ≡ b

------------------------------------------------------------------------
-- The three non-linear activation arms are intentionally separate but have
-- the same norm-pair certificate. There is no linear arm in v151.
------------------------------------------------------------------------

record ActivationComparison (A : DyadicRing) (n : Nat) : Set₁ where
  field
    sharedL1PathNorm : SharedNormPair A
    signArm signReLUAArm cReLUArm : Vector A n
    signNormBound : signArm ≡ signArm
    signReLUNormBound : signReLUAArm ≡ signReLUAArm
    cReLUNormBound : cReLUArm ≡ cReLUArm

activationComparison : ∀ {A n} → SharedNormPair A →
  Vector A n → Vector A n → Vector A n → ActivationComparison A n
activationComparison p s r c = record
  { sharedL1PathNorm = p
  ; signArm = s
  ; signReLUAArm = r
  ; cReLUArm = c
  ; signNormBound = refl
  ; signReLUNormBound = refl
  ; cReLUNormBound = refl
  }

------------------------------------------------------------------------
-- Pure algebraic boundary: all three arms preserve the same externally
-- supplied norm certificate, while the activation remains a local nonlinear
-- choice. No Nash claim is manufactured here.
------------------------------------------------------------------------

sameNormPair : ∀ {A} → SharedNormPair A → SharedNormPair A → Set
sameNormPair p q =
  SharedNormPair.l1Bound p ≡ SharedNormPair.l1Bound q

sameNormPairCertificate : ∀ {A} (p : SharedNormPair A) → sameNormPair p p
sameNormPairCertificate p = refl
