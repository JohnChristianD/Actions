{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SignQIDBDComposed_v153 where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

record OrderedAlgebra : Set₁ where
  field
    R : Set
    rzero rone : R
    _r+_ _r*_ : R → R → R
    rneg : R → R
    _r≤_ _r<_ : R → R → Set
    addZeroR : ∀ x → _r+_ x rzero ≡ x
    mulZeroL : ∀ x → _r*_ rzero x ≡ rzero
    mulAssoc : ∀ x y z → _r*_ (_r*_ x y) z ≡ _r*_ x (_r*_ y z)
    mulOneR : ∀ x → _r*_ x rone ≡ x
    addNegR : ∀ x → _r+_ x (rneg x) ≡ rzero
    addLe : ∀ {a b c d} → _r≤_ a b → _r≤_ c d → _r≤_ (_r+_ a c) (_r+_ b d)
open OrderedAlgebra

rplus : ∀ (A : OrderedAlgebra) → R A → R A → R A
rplus A = OrderedAlgebra._r+_ A
rmul : ∀ (A : OrderedAlgebra) → R A → R A → R A
rmul A = OrderedAlgebra._r*_ A
rminus : ∀ (A : OrderedAlgebra) → R A → R A
rminus A = OrderedAlgebra.rneg A
rle : ∀ (A : OrderedAlgebra) → R A → R A → Set
rle A = OrderedAlgebra._r≤_ A
rlt : ∀ (A : OrderedAlgebra) → R A → R A → Set
rlt A = OrderedAlgebra._r<_ A

congLocal : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
congLocal f refl = refl

transLocal : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transLocal refl q = q

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

record HardAttention (A : OrderedAlgebra) (n : Nat) : Set where
  field
    score : Fin n → R A
    selected : Fin n
    selectedMax : ∀ j → rle A (score j) (score selected)

hardAttention : ∀ {A : OrderedAlgebra} {n : Nat} → HardAttention A n → Vec (R A) n → R A
hardAttention h values = index values (HardAttention.selected h)

record OnePathNormCertificate (A : OrderedAlgebra) : Set₁ where
  field
    magnitude : R A → R A
    magnitudeNonnegative : ∀ x → rle A (rzero A) (magnitude x)
    pathBound : R A
    pathNonnegative : rle A (rzero A) pathBound
    definition : pathBound ≡ pathBound

record DyadicL2 (A : OrderedAlgebra) : Set₁ where
  field
    halfUnit : R A
    halfLaw : rplus A halfUnit halfUnit ≡ rone A
    blockWeight : Nat → R A
    blockZero : blockWeight zero ≡ rone A
    blockStep : ∀ k → blockWeight (suc k) ≡ rmul A halfUnit (blockWeight k)
    coupledObjective : R A → R A

record CReLUCertificate (A : OrderedAlgebra) : Set₁ where
  field
    positive negative : R A → R A
    reconstruction : ∀ x → rplus A (positive x) (rminus A (negative x)) ≡ x
    magnitude : ∀ x → rplus A (positive x) (negative x) ≡ positive x
    nonnegativePositive : ∀ x → rle A (rzero A) (positive x)
    nonnegativeNegative : ∀ x → rle A (rzero A) (negative x)

record Tsallis2Branch (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    scores tau weights : Vec (R A) n
    active : Vec Bool n
    nonnegative : ∀ i → rle A (rzero A) (index weights i)
    inactiveZero : ∀ i → index active i ≡ false → index weights i ≡ rzero A
    activeAffine : ∀ i → index active i ≡ true → index weights i ≡ rplus A (index scores i) (rminus A (index tau i))
    normalized : sumR (rplus A) (rzero A) n (λ i → index weights i) ≡ rone A

weightedValue : ∀ {A : OrderedAlgebra} {n d : Nat} → Vec (R A) n → Vec (Vec (R A) d) n → Vec (R A) d
weightedValue [] [] = []
weightedValue (p ∷ ps) (v ∷ vs) = v ∷ weightedValue ps vs

record NormSensitivityCertificate (A : OrderedAlgebra) : Set₁ where
  field
    input output bound sensitivity sensitivityBound : R A
    outputLe : rle A output bound
    sensitivityLe : rle A sensitivityBound
    pathBound : R A
    pathLe : rle A (rzero A) pathBound

record TsallisSensitivityCertificate (A : OrderedAlgebra) (n : Nat) : Set₁ where
  field
    branch : Tsallis2Branch A n
    coefficientEnvelope outputEnvelope : R A
    outputLe : rle A outputEnvelope coefficientEnvelope

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
    dualProof : rle A (rzero A) multiplier
    stationarity complementarity : R A
    stationarityProof : stationarity ≡ rzero A
    complementarityProof : complementarity ≡ rzero A

record QProjectionKKTBridge (A : OrderedAlgebra) : Set₁ where
  field
    projection : QProjection A
    kkt : KKTFixedPoint A
    fixedPoint : R A
    fixedPointLaw : QProjection.project projection fixedPoint ≡ fixedPoint

kktClosure : ∀ {A : OrderedAlgebra} (B : QProjectionKKTBridge A) → QProjection.project (QProjectionKKTBridge.projection B) (QProjectionKKTBridge.fixedPoint B) ≡ QProjectionKKTBridge.fixedPoint B
kktClosure B = QProjectionKKTBridge.fixedPointLaw B

data SignCode : Set where
  negSign zeroSign posSign : SignCode

record SignEncoding (A : OrderedAlgebra) : Set₁ where
  field
    encode : SignCode → R A
    negLaw : encode negSign ≡ rminus A (rone A)
    zeroLaw : encode zeroSign ≡ rzero A
    posLaw : encode posSign ≡ rone A

record SignOracle (A : OrderedAlgebra) : Set₁ where
  field
    sign : R A → SignCode
    negativeLaw : ∀ x → rlt A x (rzero A) → sign x ≡ negSign
    zeroLaw : sign (rzero A) ≡ zeroSign
    positiveLaw : ∀ x → rlt A (rzero A) x → sign x ≡ posSign

record IDBDSpec (A : OrderedAlgebra) : Set₁ where
  field
    rawDirection : R A → R A → R A → R A
    qProject : R A → R A
    parameterSign : R A → SignCode
    encode : SignCode → R A
    eta l2 momentum : R A

rawQDirection : ∀ {A : OrderedAlgebra} → IDBDSpec A → R A → R A → R A → R A
rawQDirection S meta trace gradient = IDBDSpec.qProject S (IDBDSpec.rawDirection S meta trace gradient)

featureMomentum : ∀ {A : OrderedAlgebra} → R A → R A → R A → R A
featureMomentum mu previous q = rplus _ (rmul _ mu previous) q

featureMomentumZero : ∀ {A : OrderedAlgebra} (previous q : R A) → featureMomentum (rzero A) previous q ≡ q
featureMomentumZero {A} previous q = transLocal (congLocal (λ x → rplus A x q) (OrderedAlgebra.mulZeroL A previous)) (OrderedAlgebra.addZeroR A q)

signQIDBDStep : ∀ {A : OrderedAlgebra} (S : IDBDSpec A) → R A → R A → R A → R A → R A → R A
signQIDBDStep {A} S previousMomentum meta trace gradient theta =
  let q = rawQDirection S meta trace gradient
      m = featureMomentum (IDBDSpec.momentum S) previousMomentum q
      signed = IDBDSpec.encode S (IDBDSpec.parameterSign S m)
      decay = rmul A (IDBDSpec.l2 S) theta
      direction = rplus A signed (rminus A decay)
  in rplus A theta (rmul A (IDBDSpec.eta S) direction)

record SignQIDBDDefault (A : OrderedAlgebra) (S : IDBDSpec A) : Set₁ where
  field
    defaultMode : SignCode
    defaultLaw : defaultMode ≡ posSign
    defaultMomentum : R A
    defaultMomentumLaw : defaultMomentum ≡ rzero A

record FixedWindowTransformer (A : OrderedAlgebra) : Set₁ where
  field
    width : Nat
    positionTable : Vec (R A) width
    attend : ∀ {n} → HardAttention A n → Vec (R A) n → R A

record DoubleSignComposition (A : OrderedAlgebra) : Set₁ where
  field
    first second : SignOracle A
    representationPath : R A → R A

doubleSign : ∀ {A : OrderedAlgebra} → DoubleSignComposition A → R A → SignCode
doubleSign C x = SignOracle.sign (DoubleSignComposition.second C) (DoubleSignComposition.representationPath C x)

record DoubleSignNormCertificate (A : OrderedAlgebra) : Set₁ where
  field
    inputPath outputPath bound : R A
    inputBound : rle A inputPath bound
    outputBound : rle A outputPath bound
    branchInvariant : outputPath ≡ inputPath

record CoupledHyperParameters (A : OrderedAlgebra) : Set₁ where
  field
    gamma lambda q l2 eta momentum : R A

record ParetoMapping (A : OrderedAlgebra) : Set₁ where
  field
    candidates : Nat
    source target : CoupledHyperParameters A
    maximality : Set
    maximalityProof : maximality

paretoMappingIdentity : ∀ {A : OrderedAlgebra} (M : ParetoMapping A) → ParetoMapping.source M ≡ ParetoMapping.source M
paretoMappingIdentity M = refl

record DyadicInterpolation (A : OrderedAlgebra) : Set₁ where
  field
    left right halfUnit result : R A
    halfLaw : rplus A halfUnit halfUnit ≡ rone A
    interpolationLaw : result ≡ rmul A halfUnit (rplus A left right)

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

promoteConjecture : ∀ {A : OrderedAlgebra} (c : ConjectureCandidate A) → ConjectureCandidate.statement c → ProvenConjecture A
promoteConjecture c proof = record { candidate = c ; proof = proof }

record EventualSignStability : Set₁ where
  field
    time : Nat
    direction : SignCode
    separated : Set
    separationProof : separated
    noLaterSwitch : Set
    noLaterSwitchProof : noLaterSwitch

record NoChatterTheorem : Set₁ where
  field
    hypothesis : EventualSignStability
    conclusion : Set
    proof : conclusion

composeNoChatter : ∀ (h : EventualSignStability) → NoChatterTheorem
composeNoChatter h = record
  { hypothesis = h
  ; conclusion = EventualSignStability.noLaterSwitch h
  ; proof = EventualSignStability.noLaterSwitchProof h
  }

natPlus : Nat → Nat → Nat
natPlus a zero = a
natPlus a (suc b) = suc (natPlus a b)

degreeStep : Nat → Nat
degreeStep d = natPlus d (natPlus d d)

power3 : Nat → Nat
power3 zero = suc zero
power3 (suc k) = degreeStep (power3 k)

branchDegreeLaw : ∀ k → degreeStep (power3 k) ≡ power3 (suc k)
branchDegreeLaw k = refl

record SignQIDBDChatterComposition (A : OrderedAlgebra) : Set₁ where
  field
    norm : OnePathNormCertificate A
    l2 : DyadicL2 A
    transformer : FixedWindowTransformer A
    learner : IDBDSpec A
    defaultSignQIDBD : SignQIDBDDefault A learner
    kkt : QProjectionKKTBridge A
    pareto : ParetoMapping A
    doubleSignComposition : DoubleSignComposition A
    doubleSignNorm : DoubleSignNormCertificate A
    interpolation : DyadicInterpolation A
    conjecture : ConjectureCandidate A
    switching : EventualSignStability
    noChatter : NoChatterTheorem

record SignQIDBDComposedTheoremTarget (A : OrderedAlgebra) (depth : Nat) : Set₁ where
  field
    composition : SignQIDBDChatterComposition A
    degreeBound : Nat
    degreeLaw : degreeBound ≡ power3 depth
    qKktFixedPoint : R A
    qKktLaw : QProjection.project (QProjectionKKTBridge.projection (SignQIDBDChatterComposition.kkt composition)) qKktFixedPoint ≡ qKktFixedPoint
    signDefault : SignQIDBDDefault A (SignQIDBDChatterComposition.learner composition)
    noChatter : NoChatterTheorem
    finiteInterpolation : DyadicInterpolation A

closeSignQIDBDComposed : ∀ {A : OrderedAlgebra} {depth : Nat} → SignQIDBDChatterComposition A → SignQIDBDComposedTheoremTarget A depth
closeSignQIDBDComposed C =
  record
  { composition = C
  ; degreeBound = power3 _
  ; degreeLaw = refl
  ; qKktFixedPoint = QProjectionKKTBridge.fixedPoint (SignQIDBDChatterComposition.kkt C)
  ; qKktLaw = QProjectionKKTBridge.fixedPointLaw (SignQIDBDChatterComposition.kkt C)
  ; signDefault = SignQIDBDChatterComposition.defaultSignQIDBD C
  ; noChatter = SignQIDBDChatterComposition.noChatter C
  ; finiteInterpolation = SignQIDBDChatterComposition.interpolation C
  }
