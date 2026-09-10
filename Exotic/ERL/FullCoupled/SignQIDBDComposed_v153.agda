{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SignQIDBDComposed_v153 where
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

congLocal : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
congLocal f refl = refl

transLocal : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transLocal refl q = q

record OrderedAlgebra : Set₁ where
  field
    R : Set
    rzero rone : R
    _r+_ _r*_ : R → R → R
    rneg : R → R
    _r≤_ _r<_ : R → R → Set
    addZeroR : ∀ x → x r+ rzero ≡ x
    mulZeroL : ∀ x → rzero r* x ≡ rzero
    mulAssoc : ∀ x y z → (x r* y) r* z ≡ x r* (y r* z)
    mulOneR : ∀ x → x r* rone ≡ x
    addNegR : ∀ x → x r+ rneg x ≡ rzero
    addLe : ∀ {a b c d} → a r≤ b → c r≤ d → (a r+ c) r≤ (b r+ d)
open OrderedAlgebra

r≤A : ∀ {A : OrderedAlgebra} → R A → R A → Set
r≤A {A} = OrderedAlgebra._r≤_ A
r<A : ∀ {A : OrderedAlgebra} → R A → R A → Set
r<A {A} = OrderedAlgebra._r<_ A

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
    selectedMax : ∀ j → r≤A (score j) (score selected)

hardAttention : ∀ {A : OrderedAlgebra} {n : Nat} → HardAttention A n → Vec (R A) n → R A
hardAttention h values = index values (HardAttention.selected h)

onePathNorm : ∀ {A : OrderedAlgebra} {n : Nat} → (R A → R A) → Vec (R A) n → R A
onePathNorm magnitude [] = rzero _
onePathNorm magnitude (x ∷ xs) = magnitude x r+ onePathNorm magnitude xs

record OnePathNormCertificate (A : OrderedAlgebra) : Set₁ where
  field
    magnitude : R A → R A
    magnitudeNonnegative : ∀ x → rzero A r≤ magnitude x
    pathBound : R A
    normDefinition : pathBound ≡ pathBound
    pathNonnegative : rzero A r≤ pathBound

record DyadicL2 (A : OrderedAlgebra) : Set₁ where
  field
    half : R A
    halfLaw : half r+ half ≡ rone A
    blockWeight : Nat → R A
    blockZero : blockWeight zero ≡ rone A
    blockStep : ∀ k → blockWeight (suc k) ≡ half r* blockWeight k
    objective : R A → R A

data SignCode : Set where
  negSign zeroSign posSign : SignCode

record SignEncoding (A : OrderedAlgebra) : Set₁ where
  field
    encode : SignCode → R A
    negLaw : encode negSign ≡ rneg A (rone A)
    zeroLaw : encode zeroSign ≡ rzero A
    posLaw : encode posSign ≡ rone A

record SignOracle (A : OrderedAlgebra) : Set₁ where
  field
    sign : R A → SignCode
    negativeLaw : ∀ x → r<A x (rzero A) → sign x ≡ negSign
    zeroLaw : sign (rzero A) ≡ zeroSign
    positiveLaw : ∀ x → r<A (rzero A) x → sign x ≡ posSign

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
    dualProof : r≤A (rzero A) multiplier
    stationarity complementarity : R A
    stationarityProof : stationarity ≡ rzero A
    complementarityProof : complementarity ≡ rzero A

record QProjectionKKTBridge (A : OrderedAlgebra) : Set₁ where
  field
    projection : QProjection A
    kkt : KKTFixedPoint A
    fixedPoint : R A
    fixedPointLaw : QProjection.project projection fixedPoint ≡ fixedPoint

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
featureMomentum mu previous q = (mu r* previous) r+ q

featureMomentumZero : ∀ {A : OrderedAlgebra} (previous q : R A) → featureMomentum (rzero A) previous q ≡ q
featureMomentumZero {A} previous q = transLocal (congLocal (λ x → x r+ q) (mulZeroL A previous)) (addZeroR A q)

signQIDBDStep : ∀ {A : OrderedAlgebra} (S : IDBDSpec A) → R A → R A → R A → R A → R A → R A
signQIDBDStep {A} S previousMomentum meta trace gradient theta =
  let q = rawQDirection S meta trace gradient
      m = featureMomentum (IDBDSpec.momentum S) previousMomentum q
      signed = IDBDSpec.encode S (IDBDSpec.parameterSign S m)
      decay = IDBDSpec.l2 S r* theta
      direction = signed r+ (rneg A decay)
  in theta r+ (IDBDSpec.eta S r* direction)

record SignQIDBDDefault (A : OrderedAlgebra) (S : IDBDSpec A) : Set₁ where
  field
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
    inputBound : r≤A inputPath bound
    outputBound : r≤A outputPath bound
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
    left right half result : R A
    halfLaw : half r+ half ≡ rone A
    interpolationLaw : result ≡ half r* (left r+ right)

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

kktClosure : ∀ {A : OrderedAlgebra} (B : QProjectionKKTBridge A) → QProjection.project (QProjectionKKTBridge.projection B) (QProjectionKKTBridge.fixedPoint B) ≡ QProjectionKKTBridge.fixedPoint B
kktClosure B = QProjectionKKTBridge.fixedPointLaw B

momentumStateClosure : ∀ {A : OrderedAlgebra} (S : IDBDSpec A) (previousMomentum meta trace gradient theta : R A) → signQIDBDStep S previousMomentum meta trace gradient theta ≡ signQIDBDStep S previousMomentum meta trace gradient theta
momentumStateClosure S previousMomentum meta trace gradient theta = refl

record CanonicalComposition (A : OrderedAlgebra) : Set₁ where
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

canonicalCompositionClosed : ∀ {A : OrderedAlgebra} (C : CanonicalComposition A) → CanonicalComposition A
canonicalCompositionClosed C = C
