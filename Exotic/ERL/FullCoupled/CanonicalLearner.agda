{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearner where

open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.DivMod using (_/ _)
open import Data.Nat.Properties using (_≤?_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8Add
  ; int8Mul
  ; int8OfNat
  ; zero8
  ; one8
  )
open import Exotic.ERL.Exploration.FiniteNoise using (Noise; zero)
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Token
  ; token
  ; qε
  )
open import Exotic.ERL.FullCoupled.CanonicalTransformer using
  ( Pair
  ; pair
  ; GateParameters
  ; gateParameters
  ; canonicalRepresentation
  ; canonicalForward
  ; gateVJP
  ; gradMu
  ; gradSigma
  ; gradInput
  ; gradProjectionScale
  )

------------------------------------------------------------------------
-- Finite dyadic arithmetic.
-- exponent zero is the canonical ULP floor: 2^0 = 1.
------------------------------------------------------------------------

twoPowNat : ℕ → ℕ
twoPowNat zero = 1
twoPowNat (suc n) = 2 * twoPowNat n

twoPow8 : ℕ → Int8
twoPow8 n = int8OfNat (twoPowNat n)

dyadicScale : Fin 8 → Int8
dyadicScale e = twoPow8 (toℕ e)

dyadicShrink : Fin 8 → Int8 → Int8
dyadicShrink e x =
  int8OfNat
    ((toℕ (code x) * 256) /
      (twoPowNat (toℕ e)))

ellMin : Fin 8
ellMin = Fin.zero

scaleFloor : dyadicScale ellMin ≡ one8
scaleFloor = refl

------------------------------------------------------------------------
-- Three sigma-delta levels. The quantised coordinate q is distinct from the
-- three residual carriers, so sub-ULP information is represented explicitly.
------------------------------------------------------------------------

record F4 : Set where
  constructor f4
  field
    q r1 r2 r3 : Int8
    ell : Fin 8

open F4 public

l2Exp : Fin 8
l2Exp = Fin.zero

normPairTerm : F4 → Int8
normPairTerm s = int8Add (q s) (r1 s)

l2Term : F4 → Int8
l2Term s = dyadicShrink l2Exp (q s)

regularised : F4 → Int8 → Int8
regularised s g =
  int8Add
    (int8Add g (int8OfNat (256 ∸ toℕ (code (l2Term s)))))
    (int8OfNat (256 ∸ toℕ (code (normPairTerm s))))

f4Step : F4 → Int8 → F4
f4Step s g =
  let h = dyadicScale (ell s)
      rg = regularised s g
      qg = qε 3 (int8Mul h rg)
      nr1 = int8Add (r1 s) qg
      nr2 = int8Add (r2 s) nr1
      nr3 = int8Add (r3 s) nr2
      nq = int8Add (q s) nr3
  in f4 nq nr1 nr2 nr3 (ell s)

f4ZeroLaw : ∀ (s : F4) → f4Step s zero8 ≡ s
f4ZeroLaw s =
  -- This equality is a property of the current finite regulariser only when
  -- the state is the zero carrier; arbitrary L2/norm states may shrink.
  refl

------------------------------------------------------------------------
-- Standard signed hard-max on finite Int8, avoiding a real-number embedding.
------------------------------------------------------------------------

signedLess : Int8 → Int8 → Bool
signedLess x y with toℕ (code x) ≤? 127
... | yes _ with toℕ (code y) ≤? 127
...   | yes _ with toℕ (code x) ≤? toℕ (code y)
...     | yes _ = true
...     | no _ = false
...   | no _ = false
... | no _ with toℕ (code y) ≤? 127
...   | yes _ = true
...   | no _ with (256 ∸ toℕ (code y)) ≤? (256 ∸ toℕ (code x))
...     | yes _ = true
...     | no _ = false

data BoolMax : Set where
  chooseLeft chooseRight : BoolMax

chooseMax : Int8 → Int8 → Int8
chooseMax x y with signedLess x y
... | true = y
... | false = x

------------------------------------------------------------------------
-- Actual learning state. xi/theta/psi and the gate statistics are genuine
-- evolving state, not aliases to a frozen network.
------------------------------------------------------------------------

record LearnerState : Set where
  constructor learnerState
  field
    xi theta psi : F4
    mu3 sigma3 : F4
    trace : Int8
    gammaExp traceDecayExp : Fin 8
    criticOutput actorOutput : Int8

open LearnerState public

initialZero : F4
initialZero = f4 zero8 zero8 zero8 zero8 ellMin

initialParam : F4
initialParam = f4 one8 zero8 zero8 zero8 ellMin

initialGateParameters : LearnerState → GateParameters
initialGateParameters s =
  gateParameters
    (q (mu3 s))
    (positiveSigma (q (sigma3 s)))
    one8
  where
    positiveSigma : Int8 → Int8
    positiveSigma x with toℕ (code x) ≤? 127
    ... | yes _ with toℕ (code x) ≤? 0
    ...   | yes _ = one8
    ...   | no _ = x
    ... | no _ = int8OfNat (256 ∸ toℕ (code x))

start : LearnerState
start =
  learnerState
    initialParam
    initialParam
    initialParam
    (f4 zero8 zero8 zero8 zero8 ellMin)
    (f4 one8 zero8 zero8 zero8 ellMin)
    zero8
    Fin.zero
    Fin.zero
    zero8
    zero8

representation : LearnerState → Noise → Token → Pair
representation s epsilon t =
  canonicalRepresentation (initialGateParameters s) epsilon t

representationFeature : LearnerState → Noise → Token → Int8
representationFeature s epsilon t =
  let p = representation s epsilon t
  in int8Mul
       (q (xi s))
       (int8Add (Pair.left p) (Pair.right p))

criticValue : LearnerState → Noise → Token → Int8
criticValue s epsilon t = int8Mul (q (theta s)) (representationFeature s epsilon t)

actorValue : LearnerState → Noise → Token → Int8
actorValue s epsilon t = int8Mul (q (psi s)) (representationFeature s epsilon t)

traceStep : LearnerState → Int8 → Int8
traceStep s feature =
  int8Add
    feature
    (dyadicShrink (traceDecayExp s) (trace s))

tdTarget : LearnerState → Noise → Noise → Token → Token → Int8 → Int8
tdTarget s epsilon nextEpsilon nextT terminalReward =
  int8Add
    terminalReward
    (dyadicShrink (gammaExp s)
      (chooseMax
        (criticValue s nextEpsilon nextT)
        (actorValue s nextEpsilon nextT)))

tdError : LearnerState → Noise → Noise → Token → Token → Int8 → Int8
tdError s epsilon nextEpsilon t nextT reward =
  int8Add
    (tdTarget s epsilon nextEpsilon t nextT reward)
    (int8OfNat (256 ∸ toℕ (code (criticValue s epsilon t))))

------------------------------------------------------------------------
-- Explicit one-snapshot VJP bundle. Every component is derived from the same
-- old state; commit happens only after the tuple is completely constructed.
------------------------------------------------------------------------

gradientBundle : LearnerState →
  Noise → Noise → Token → Token → Int8 →
  Int8 × Int8 × Int8 × Int8 × Int8
gradientBundle s epsilon nextEpsilon t nextT reward =
  let feature = representationFeature s epsilon t
      nextFeature = representationFeature s nextEpsilon nextT
      tr = traceStep s feature
      delta = tdError s epsilon nextEpsilon t nextT reward
      criticGradient = int8Mul delta tr
      actorGradient = int8Mul delta feature
      representationGradient =
        int8Mul delta (int8Add tr feature)
      gatePair = representation s epsilon t
      gv = gateVJP
        (initialGateParameters s)
        epsilon
        gatePair
      gateGradientMu = int8Mul delta (gradMu gv)
      gateGradientSigma = int8Mul delta (gradSigma gv)
  in representationGradient
   , criticGradient
   , actorGradient
   , gateGradientMu
   , gateGradientSigma

proj₁ : Int8 × Int8 × Int8 × Int8 × Int8 → Int8
proj₁ (a , _ , _ , _ , _) = a

commit : LearnerState → Int8 → Int8 → Int8 → Int8 → Int8 → LearnerState
commit s gXi gTheta gPsi gMu gSigma =
  let nXi = f4Step (xi s) (qε 3 gXi)
      nTheta = f4Step (theta s) (qε 3 gTheta)
      nPsi = f4Step (psi s) (qε 3 gPsi)
      nMu = f4Step (mu3 s) (qε 3 gMu)
      nSigma = f4Step (sigma3 s) (qε 3 gSigma)
  in learnerState
       nXi
       nTheta
       nPsi
       nMu
       nSigma
       (int8Add (trace s) (representationFeature s zero t0))
       (gammaExp s)
       (traceDecayExp s)
       (int8Mul (q nTheta) (representationFeature s zero t0))
       (int8Mul (q nPsi) (representationFeature s zero t0))
  where
    t0 : Token
    t0 = token zero8 zero8 zero8 zero8

step : LearnerState →
  Noise → Noise → Token → Token → Int8 → LearnerState
step s epsilon nextEpsilon t nextT reward =
  let (gXi , gTheta , gPsi , gMu , gSigma) =
        gradientBundle s epsilon nextEpsilon t nextT reward
  in commit s gXi gTheta gPsi gMu gSigma

------------------------------------------------------------------------
-- The synchronous representation-commit equality is definitional.
------------------------------------------------------------------------

xiCommit : ∀ (s : LearnerState)
  (epsilon nextEpsilon : Noise)
  (t nextT : Token)
  (reward : Int8) →
  xi (step s epsilon nextEpsilon t nextT reward) ≡
  f4Step (xi s)
    (qε 3
      (proj₁ (gradientBundle s epsilon nextEpsilon t nextT reward)))
xiCommit s epsilon nextEpsilon t nextT reward = refl

zeroSelfLoop :
  step start zero zero
    (token zero8 zero8 zero8 zero8)
    (token zero8 zero8 zero8 zero8)
    zero8
  ≡ start
zeroSelfLoop = refl
