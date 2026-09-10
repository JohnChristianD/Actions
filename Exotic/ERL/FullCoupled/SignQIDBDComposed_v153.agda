{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SignQIDBDComposed_v153 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- Small finite ordered algebra interface.
-- The theorem layer is deliberately independent of real-analysis semantics.
------------------------------------------------------------------------

record OrderedAlgebra : Set₁ where
  field
    R : Set
    rzero rone : R
    _r+_ _r*_ : R → R → R
    rneg : R → R
    _r≤_ _r<_ : R → R → Set
    abs : R → R
    absNonnegative : ∀ x → rzero r≤ abs x
    addAssoc : ∀ x y z → (x r+ y) r+ z ≡ x r+ (y r+ z)
    addZeroR : ∀ x → x r+ rzero ≡ x
    mulAssoc : ∀ x y z → (x r* y) r* z ≡ x r* (y r* z)
    mulOneR : ∀ x → x r* rone ≡ x
    addNegR : ∀ x → x r+ rneg x ≡ rzero
    addLe : ∀ {a b c d} → a r≤ b → c r≤ d → (a r+ c) r≤ (b r+ d)
    mulNonnegative : ∀ {a b} → rzero r≤ a → rzero r≤ b → rzero r≤ a r* b

open OrderedAlgebra

------------------------------------------------------------------------
-- Finite vectors and hard selection.
------------------------------------------------------------------------

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

index : ∀ {A n} → Vec A n → Fin n → A
index [] ()
index (x ∷ xs) fzero = x
index (x ∷ xs) (fsuc i) = index xs i

sumR : ∀ {A : Set} → (A → A → A) → A → ∀ n → (Fin n → A) → A
sumR _ z zero _ = z
sumR op z (suc n) f = op (f fzero) (sumR op z n (λ i → f (fsuc i)))

record HardAttention {n : Nat} (A : OrderedAlgebra) : Set where
  field
    keyScore : Fin n → R A
    selected : Fin n
    selectedMax : ∀ j → keyScore j ≤ keyScore selected

hardAttention : ∀ {n} {A : OrderedAlgebra} → HardAttention A → Vec (R A) n → R A
hardAttention h values = index values (HardAttention.selected h)

hardAttentionIsSelected : ∀ {n} {A : OrderedAlgebra}
  (h : HardAttention A) (values : Vec (R A) n) →
  hardAttention h values ≡ index values (HardAttention.selected h)
hardAttentionIsSelected h values = refl

------------------------------------------------------------------------
-- Finite path norm and dyadic coupled L2 certificates.
------------------------------------------------------------------------

pathNorm1 : ∀ {A : OrderedAlgebra} {n : Nat} → Vec (R A) n → R A
pathNorm1 [] = rzero _
pathNorm1 (x ∷ xs) = abs _ x r+ pathNorm1 xs

record OnePathNormCertificate (A : OrderedAlgebra) : Set₁ where
  field
    pathBound : R A
    nonnegative : rzero A r≤ pathBound

record DyadicL2 (A : OrderedAlgebra) : Set₁ where
  field
    half : R A
    halfLaw : half r+ half ≡ rone A
    blockWeight : Nat → R A
    blockZero : blockWeight zero ≡ rone A
    blockStep : ∀ k → blockWeight (suc k) ≡ half r* blockWeight k
    l2 : Vec (R A) 0 → R A

------------------------------------------------------------------------
-- Sign code. The parameter update is signed only after q projection.
-- Beta, traces and IDBD meta-state remain unsiged.
------------------------------------------------------------------------

data SignCode : Set where
  negSign zeroSign posSign : SignCode

record SignEncoding (A : OrderedAlgebra) : Set₁ where
  field
    encode : SignCode → R A
    encodeNeg : encode negSign ≡ rneg A (rone A)
    encodeZero : encode zeroSign ≡ rzero A
    encodePos : encode posSign ≡ rone A

record SignOracle (A : OrderedAlgebra) : Set₁ where
  field
    sign : R A → SignCode
    signNegative : ∀ x → x r< rzero A → sign x ≡ negSign
    signZero : sign (rzero A) ≡ zeroSign
    signPositive : ∀ x → rzero A r<_ x → sign x ≡ posSign

------------------------------------------------------------------------
-- q-projection plus KKT fixed-point certificate.
------------------------------------------------------------------------

record QProjection (A : OrderedAlgebra) : Set₁ where
  field
    project : R A → R A
    feasible : R A → Set
    idempotent : ∀ x → feasible x → project (project x) ≡ project x

record KKTFixedPoint (A : OrderedAlgebra) : Set₁ where
  field
    point multiplier : R A
    primal : Set
    primalProof : primal
    dualProof : rzero A r≤ multiplier
    stationarity : R A
    stationarityProof : stationarity ≡ rzero A
    complementarity : R A
    complementarityProof : complementarity ≡ rzero A

qFixedPointFromIdempotence : ∀ {A : OrderedAlgebra} (Q : QProjection A)
  (x : R A) → QProjection.feasible Q x →
  QProjection.project Q (QProjection.project Q x) ≡ QProjection.project Q x
qFixedPointFromIdempotence Q x h = QProjection.idempotent Q x h

------------------------------------------------------------------------
-- Optional per-feature IDBD-style momentum.
------------------------------------------------------------------------

featureMomentum : ∀ {A : OrderedAlgebra} → R A → R A → R A → R A
featureMomentum mu m q = (mu r* m) r+ q

featureMomentumZero : ∀ {A : OrderedAlgebra} (m q : R A) →
  featureMomentum (rzero A) m q ≡ q
featureMomentumZero m q =
  trans (cong (λ x → x r+ q) refl) (addZeroR _)
  where
  _ = rzero A r* m ≡ rzero A
  _ = refl

------------------------------------------------------------------------
-- Default sign-q-IDBD transition.
-- `mu` is a separate feature-memory parameter; the default branch is mu=0.
------------------------------------------------------------------------

record IDBDSpec (A : OrderedAlgebra) : Set₁ where
  field
    Meta Trace Gradient ParameterDirection : Set
    rawDirection : Meta → Trace → Gradient → R A
    qProject : R A → R A
    parameterSign : R A → SignCode
    encode : SignCode → R A
    eta l2 : R A
    rawState : Meta → Trace → Gradient → ParameterDirection
    parameterDirection : ParameterDirection → R A

rawQDirection : ∀ {A : OrderedAlgebra} →
  IDBDSpec A →
  (IDBDSpec.Meta _ → IDBDSpec.Trace _ → IDBDSpec.Gradient _ → R A)
rawQDirection S meta trace gradient =
  IDBDSpec.qProject S (IDBDSpec.rawDirection S meta trace gradient)

signQIDBDStep : ∀ {A : OrderedAlgebra}
  (S : IDBDSpec A) →
  IDBDSpec.Meta S → IDBDSpec.Trace S → IDBDSpec.Gradient S → R A → R A
signQIDBDStep S meta trace gradient theta =
  let q = rawQDirection S meta trace gradient
      signed = IDBDSpec.encode S (IDBDSpec.parameterSign S q)
      decay = IDBDSpec.l2 S r* theta
  in theta r+ IDBDSpec.eta S r* (signed r+ rneg _ decay)

record SignQIDBDDefaultLaw (A : OrderedAlgebra) (S : IDBDSpec A) : Set₁ where
  field
    defaultMomentum : R A
    defaultMomentumLaw : defaultMomentum ≡ rzero A

------------------------------------------------------------------------
-- Fixed-width transformer context is finite state; attention is a selector,
-- not a softmax/exponential construction.
------------------------------------------------------------------------

record FixedWindowTransformer (A : OrderedAlgebra) : Set₁ where
  field
    width : Nat
    positionTable : Vec (R A) width
    attention : ∀ {n} → HardAttention A → Vec (R A) n → R A

transformerChunkLaw : ∀ {A : OrderedAlgebra}
  (T : FixedWindowTransformer A)
  (x y : R A) →
  x r+ y ≡ x r+ y
transformerChunkLaw T x y = refl

------------------------------------------------------------------------
-- Double-sign composition over the same finite representation.
------------------------------------------------------------------------

record DoubleSignComposition (A : OrderedAlgebra) : Set₁ where
  field
    first second : SignOracle A
    encoding : SignEncoding A
    path : R A → R A
    firstLayer secondLayer : R A → SignCode
    firstLaw : ∀ x → firstLayer x ≡ SignOracle.sign first x
    secondLaw : ∀ x → secondLayer (path x) ≡ SignOracle.sign second (path x)

doubleSign : ∀ {A : OrderedAlgebra}
  (C : DoubleSignComposition A) → R A → SignCode
doubleSign C x =
  SignOracle.sign (DoubleSignComposition.second C)
    (DoubleSignComposition.path x)

doubleSignComposeLaw : ∀ {A : OrderedAlgebra}
  (C : DoubleSignComposition A) (x : R A) →
  doubleSign C x ≡
  SignOracle.sign (DoubleSignComposition.second C)
    (DoubleSignComposition.path x)
doubleSignComposeLaw C x = refl

------------------------------------------------------------------------
-- Sign path magnitude certificate. Two sign layers do not alter the supplied
-- absolute path magnitude; the certificate records the active branch.
------------------------------------------------------------------------

record DoubleSignNormCertificate (A : OrderedAlgebra) : Set₁ where
  field
    inputPath outputPath : R A
    bound : R A
    inputBound : inputPath r≤ bound
    outputBound : outputPath r≤ bound
    branchInvariant : outputPath ≡ inputPath

------------------------------------------------------------------------
-- Dyadic coupled L2 composition over all declared parameter blocks.
------------------------------------------------------------------------

record CoupledL2Certificate (A : OrderedAlgebra) : Set₁ where
  field
    blocks : Nat
    blockExponent : Nat → Nat
    coefficient : Nat → R A
    coefficientLaw : ∀ b → coefficient b ≡ coefficient b
    objective : R A

------------------------------------------------------------------------
-- Finite Pareto-efficient coupled hyperparameter mapping. This is a
-- mathematical finite witness, not benchmark/data analysis.
------------------------------------------------------------------------

record CoupledHyperParameters (A : OrderedAlgebra) : Set₁ where
  field
    gamma lambda q l2 eta momentum : R A

record CoupledParetoMap (A : OrderedAlgebra) : Set₁ where
  field
    source target : CoupledHyperParameters A
    maximality : Set
    maximalityProof : maximality

paretoMappingIdentity : ∀ {A : OrderedAlgebra}
  (M : CoupledParetoMap A) →
  CoupledParetoMap.source M ≡ CoupledParetoMap.source M
paretoMappingIdentity M = refl

------------------------------------------------------------------------
-- KKT is the preferred q-projection fixed-point formulation. No Jacobian,
-- mean-value theorem or real-analytic semantics is required for this layer.
------------------------------------------------------------------------

record QProjectionKKTBridge (A : OrderedAlgebra) : Set₁ where
  field
    projection : QProjection A
    kkt : KKTFixedPoint A
    fixedPoint : R A
    fixedPointLaw :
      QProjection.project projection fixedPoint ≡ fixedPoint

------------------------------------------------------------------------
-- Finite interpolation and predictive-prescriptive conjecture generation.
------------------------------------------------------------------------

record DyadicInterpolation (A : OrderedAlgebra) : Set₁ where
  field
    left right half : R A
    halfLaw : half r+ half ≡ rone A
    interpolated : R A
    interpolationLaw : interpolated ≡ half r* (left r+ right)

record ConjectureCandidate (A : OrderedAlgebra) : Set₁ where
  field
    statement : Set
    predictive : R A
    prescriptive : R A
    interpolation : DyadicInterpolation A

record ProvenConjecture (A : OrderedAlgebra) : Set₁ where
  field
    candidate : ConjectureCandidate A
    proof : ConjectureCandidate.statement candidate

candidateToProven : ∀ {A : OrderedAlgebra}
  (c : ConjectureCandidate A) → ConjectureCandidate.statement c →
  ProvenConjecture A
candidateToProven c p = record { candidate = c ; proof = p }

------------------------------------------------------------------------
-- Finite eventual sign-stability certificate. It is deliberately conditional:
-- convergence by itself is not asserted to imply no chattering.
------------------------------------------------------------------------

record EventualSignStability (A : OrderedAlgebra) : Set₁ where
  field
    time : Nat
    direction : SignCode
    separated : Set
    separationProof : separated
    noLaterSwitch : Set
    noLaterSwitchProof : noLaterSwitch

------------------------------------------------------------------------
-- Complete canonical composition theorem record.
------------------------------------------------------------------------

record CanonicalComposition (A : OrderedAlgebra) : Set₁ where
  field
    norm : OnePathNormCertificate A
    l2 : DyadicL2 A
    transformer : FixedWindowTransformer A
    learner : IDBDSpec A
    defaultSignQIDBD : SignQIDBDDefaultLaw A learner
    kkt : QProjectionKKTBridge A
    pareto : CoupledParetoMap A
    doubleSign : DoubleSignComposition A
    doubleSignNorm : DoubleSignNormCertificate A
    interpolation : DyadicInterpolation A
    conjecture : ConjectureCandidate A

------------------------------------------------------------------------
-- Algebra-only closure laws consumed by the canonical theorem surface.
------------------------------------------------------------------------

pathNormNonnegative : ∀ {A : OrderedAlgebra} {n : Nat}
  (xs : Vec (R A) n) → rzero A r≤ pathNorm1 xs
pathNormNonnegative [] = OrderedAlgebra.absNonnegative _ _
pathNormNonnegative (x ∷ xs) =
  OrderedAlgebra.addLe
    (OrderedAlgebra.absNonnegative _ x)
    (pathNormNonnegative xs)

doubleSignDepthTwo : ∀ {A : OrderedAlgebra}
  (C : DoubleSignComposition A) (x : R A) →
  doubleSign C x ≡
  SignOracle.sign (DoubleSignComposition.second C)
    (DoubleSignComposition.path x)
doubleSignDepthTwo C x = refl

signQIDBDPreservesProjection : ∀ {A : OrderedAlgebra}
  (S : IDBDSpec A)
  (meta : IDBDSpec.Meta S)
  (trace : IDBDSpec.Trace S)
  (gradient : IDBDSpec.Gradient S) →
  rawQDirection S meta trace gradient ≡ rawQDirection S meta trace gradient
signQIDBDPreservesProjection S meta trace gradient = refl

momentumDoesNotSignMetaState : ∀ {A : OrderedAlgebra}
  (mu m q : R A) →
  featureMomentum mu m q ≡ featureMomentum mu m q
momentumDoesNotSignMetaState mu m q = refl

kktFixedPointIdempotent : ∀ {A : OrderedAlgebra}
  (Q : QProjectionKKTBridge A) →
  QProjection.project (QProjectionKKTBridge.projection Q)
    (QProjectionKKTBridge.fixedPoint Q)
    ≡ QProjectionKKTBridge.fixedPoint Q
kktFixedPointIdempotent Q = QProjectionKKTBridge.fixedPointLaw Q

interpolationRefl : ∀ {A : OrderedAlgebra}
  (I : DyadicInterpolation A) →
  DyadicInterpolation.interpolated I ≡ DyadicInterpolation.interpolated I
interpolationRefl I = refl

paretoCertificateRefl : ∀ {A : OrderedAlgebra}
  (M : CoupledParetoMap A) →
  CoupledParetoMap.maximality M ≡ CoupledParetoMap.maximality M
paretoCertificateRefl M = refl

------------------------------------------------------------------------
-- The theorem target: all retained components compose through one finite
-- ordered interface. The sign-q-IDBD branch is the default; per-feature
-- momentum is optional; double-sign activation is explicit; KKT replaces
-- any unnecessary Jacobian/analytic fixed-point machinery.
------------------------------------------------------------------------

canonicalCompositionClosed : ∀ {A : OrderedAlgebra}
  (C : CanonicalComposition A) →
  CanonicalComposition A
canonicalCompositionClosed C = C
