{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearner where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Fin as F using (Fin; toℕ)
open import Data.Nat using (ℕ; zero; suc; _*_ ; _+_; _∸_)
open import Data.Nat.DivMod using (_/_)
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
open import Exotic.ERL.FullCoupled.CanonicalToken using
  ( Token
  ; token
  )
open import Exotic.ERL.FullCoupled.CanonicalFinitePrimitives using
  ( qε
  )
open import Exotic.ERL.FullCoupled.CanonicalTransformer using
  ( Pair
  ; GateParameters
  ; gateParameters
  ; canonicalRepresentation
  ; gateVJP
  ; gradMu
  ; gradSigma
  )

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
      (256 * twoPowNat (toℕ e)))

ellMin : Fin 8
ellMin = F.zero

scaleFloor : dyadicScale ellMin ≡ one8
scaleFloor = refl

record F4 : Set where
  constructor f4
  field
    q r1 r2 r3 : Int8
    ell : Fin 8

open F4 public

l2Exp : Fin 8
l2Exp = F.zero

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

qProjectedIDBDStep : F4 → Int8 → Int8 → F4
qProjectedIDBDStep s delta eligibility =
  f4Step s (int8Mul delta eligibility)

qProjectedIDBDLaw : ∀ (s : F4) (delta eligibility : Int8) →
  qProjectedIDBDStep s delta eligibility ≡
  f4Step s (int8Mul delta eligibility)
qProjectedIDBDLaw s delta eligibility = refl

initialZero : F4
initialZero = f4 zero8 zero8 zero8 zero8 ellMin

initialParam : F4
initialParam = f4 one8 zero8 zero8 zero8 ellMin

f4ZeroWitness : f4Step initialZero zero8 ≡ initialZero
f4ZeroWitness = refl

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

chooseMax : Int8 → Int8 → Int8
chooseMax x y with signedLess x y
... | true = y
... | false = x

record LearnerState : Set where
  constructor learnerState
  field
    xi theta psi : F4
    mu3 sigma3 : F4
    trace : Int8
    gammaExp traceDecayExp : Fin 8
    criticOutput actorOutput : Int8

open LearnerState public

positiveSigma : Int8 → Int8
positiveSigma x with toℕ (code x) ≤? 127
... | yes _ with toℕ (code x) ≤? 0
...   | yes _ = one8
...   | no _ = x
... | no _ = int8OfNat (256 ∸ toℕ (code x))

gateParametersOf : LearnerState → GateParameters
gateParametersOf s =
  gateParameters
    (q (mu3 s))
    (positiveSigma (q (sigma3 s)))
    one8

start : LearnerState
start =
  learnerState
    initialParam
    initialParam
    initialParam
    initialZero
    initialParam
    zero8
    F.zero
    F.zero
    zero8
    zero8

representation : LearnerState → Noise → Token → Pair
representation s epsilon t =
  canonicalRepresentation (gateParametersOf s) epsilon t

representationFeature : LearnerState → Noise → Token → Int8
representationFeature s epsilon t =
  let p = representation s epsilon t
  in int8Mul
       (q (xi s))
       (int8Add (Pair.left p) (Pair.right p))

criticValue : LearnerState → Noise → Token → Int8
criticValue s epsilon t =
  int8Mul (q (theta s)) (representationFeature s epsilon t)

actorValue : LearnerState → Noise → Token → Int8
actorValue s epsilon t =
  int8Mul (q (psi s)) (representationFeature s epsilon t)

traceStep : LearnerState → Int8 → Int8
traceStep s feature =
  int8Add
    feature
    (dyadicShrink (traceDecayExp s) (trace s))

tdTarget : LearnerState → Noise → Token → Int8 → Int8
tdTarget s nextEpsilon nextT reward =
  int8Add
    reward
    (dyadicShrink (gammaExp s)
      (chooseMax
        (criticValue s nextEpsilon nextT)
        (actorValue s nextEpsilon nextT)))

tdError : LearnerState → Noise → Noise → Token → Token → Int8 → Int8
tdError s epsilon nextEpsilon t nextT reward =
  int8Add
    (tdTarget s nextEpsilon nextT reward)
    (int8OfNat
      (256 ∸ toℕ (code (criticValue s epsilon t))))

gradientBundle : LearnerState →
  Noise → Noise → Token → Token → Int8 →
  Int8 × Int8 × Int8 × Int8 × Int8
gradientBundle s epsilon nextEpsilon t nextT reward =
  let feature = representationFeature s epsilon t
      tr = traceStep s feature
      delta = tdError s epsilon nextEpsilon t nextT reward
      criticGradient = int8Mul delta tr
      actorGradient = int8Mul delta feature
      representationGradient = int8Mul delta (int8Add tr feature)
      gv = gateVJP
        (gateParametersOf s)
        epsilon
        (representation s epsilon t)
      gateGradientMu = int8Mul delta (gradMu gv)
      gateGradientSigma = int8Mul delta (gradSigma gv)
  in representationGradient
   , criticGradient
   , actorGradient
   , gateGradientMu
   , gateGradientSigma

proj₁ : Int8 × Int8 × Int8 × Int8 × Int8 → Int8
proj₁ (a , _ , _ , _ , _) = a

commit : LearnerState →
  Int8 → Int8 → Int8 → Int8 → Int8 →
  Int8 → Int8 → Int8 → LearnerState
commit s gXi gTheta gPsi gMu gSigma newTrace newCritic newActor =
  let nXi = qProjectedIDBDStep (xi s) gXi one8
      nTheta = qProjectedIDBDStep (theta s) gTheta one8
      nPsi = qProjectedIDBDStep (psi s) gPsi one8
      nMu = qProjectedIDBDStep (mu3 s) gMu one8
      nSigma = qProjectedIDBDStep (sigma3 s) gSigma one8
  in learnerState
       nXi nTheta nPsi
       nMu nSigma
       newTrace
       (gammaExp s)
       (traceDecayExp s)
       newCritic
       newActor

step : LearnerState →
  Noise → Noise → Token → Token → Int8 → LearnerState
step s epsilon nextEpsilon t nextT reward =
  let feature = representationFeature s epsilon t
      newTrace = traceStep s feature
      newCritic = criticValue s epsilon t
      newActor = actorValue s epsilon t
      (gXi , gTheta , gPsi , gMu , gSigma) =
        gradientBundle s epsilon nextEpsilon t nextT reward
  in commit s gXi gTheta gPsi gMu gSigma
       newTrace newCritic newActor

xiCommit : ∀ (s : LearnerState)
  (epsilon nextEpsilon : Noise)
  (t nextT : Token)
  (reward : Int8) →
  xi (step s epsilon nextEpsilon t nextT reward) ≡
  qProjectedIDBDStep (xi s)
    (proj₁ (gradientBundle s epsilon nextEpsilon t nextT reward))
    one8
xiCommit s epsilon nextEpsilon t nextT reward = refl

zeroSelfLoop :
  step start zero zero
    (token zero8 zero8 zero8 zero8)
    (token zero8 zero8 zero8 zero8)
    zero8
  ≡ start
zeroSelfLoop = refl
