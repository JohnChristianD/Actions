{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearner where

open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; _∸_)
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
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Token
  ; token
  ; qε
  )
open import Exotic.ERL.FullCoupled.CanonicalTransformer using
  ( GateParameters
  ; gateParameters
  ; canonicalForward
  ; gateScalarVJP
  ; gradMu
  ; gradSigma
  )

------------------------------------------------------------------------
-- Finite dyadic scale. exponent zero is the required ULP floor.
------------------------------------------------------------------------

twoPow : ℕ → Int8
twoPow 0 = one8
twoPow (n) = int8Add (twoPow (n ∸ 1)) (twoPow (n ∸ 1))

dyadicScale : Fin 8 → Int8
dyadicScale e = twoPow (toℕ e)

ellMin : Fin 8
ellMin = Fin.zero

scaleFloor : dyadicScale ellMin ≡ one8
scaleFloor = refl

------------------------------------------------------------------------
-- Three finite sigma-delta accumulation levels.
------------------------------------------------------------------------

record F4 : Set where
  constructor f4
  field
    q r1 r2 r3 : Int8
    ell : Fin 8

open F4 public

f4Step : F4 → Int8 → F4
f4Step s g =
  let h = dyadicScale (ell s)
      qg = qε 3 (int8Mul h g)
      nr1 = int8Add (r1 s) qg
      nr2 = int8Add (r2 s) nr1
      nr3 = int8Add (r3 s) nr2
      nq = int8Add (q s) nr3
  in f4 nq nr1 nr2 nr3 (ell s)

f4ZeroLaw : ∀ (s : F4) → f4Step s zero8 ≡ s
f4ZeroLaw s = refl

------------------------------------------------------------------------
-- Actual learning state. Every learnable block is changed by `commit` from
-- one immutable snapshot.
------------------------------------------------------------------------

record LearnerState : Set where
  constructor learnerState
  field
    xi theta psi : F4
    gateParams : GateParameters
    mu3 sigma3 : F4
    trace : Int8
    gamma lambda : Int8
    criticOutput actorOutput : Int8

open LearnerState public

initialF4 : F4
initialF4 = f4 zero8 zero8 zero8 zero8 ellMin

initialGate : GateParameters
initialGate = gateParameters zero8 one8 one8

start : LearnerState
start = learnerState
  initialF4 initialF4 initialF4
  initialGate initialF4 initialF4
  zero8 one8 one8 zero8 zero8

signedMagnitude : Int8 → ℕ
signedMagnitude x with toℕ (code x) ≤? 127
... | yes _ = toℕ (code x)
... | no _ = 256 ∸ toℕ (code x)

hardMax : Int8 → Int8 → Int8
hardMax x y with signedMagnitude x ≤? signedMagnitude y
... | yes _ = y
... | no _ = x

representationFeature : LearnerState → Token → Int8
representationFeature s t =
  int8Mul (q (xi s)) (canonicalForward (gateParams s) t)

traceStep : LearnerState → Int8 → Int8
traceStep s feature =
  int8Add feature
    (int8Mul (gamma s) (int8Mul (lambda s) (trace s)))

tdTarget : LearnerState → Int8 → Int8 → Int8 → Int8
tdTarget s reward nextCritic nextActor =
  int8Add reward (hardMax nextCritic nextActor)

tdError : LearnerState → Int8 → Int8 → Int8 → Int8 → Int8
tdError s reward nextCritic nextActor =
  int8Add
    (tdTarget s reward nextCritic nextActor)
    (int8OfNat (256 ∸ toℕ (code (criticOutput s))))

gradientBundle : LearnerState → Token → Token → Int8 →
  Int8 × Int8 × Int8 × Int8 × Int8
gradientBundle s t nextT reward =
  let feature = representationFeature s t
      nextFeature = representationFeature s nextT
      nextCritic = int8Add
        (int8Mul (q (theta s)) nextFeature)
        (q (theta s))
      nextActor = int8Add
        (int8Mul (q (psi s)) nextFeature)
        (q (psi s))
      tr = traceStep s feature
      delta = tdError s reward nextCritic nextActor
      gTheta = int8Mul delta tr
      gPsi = int8Mul delta feature
      gXi = int8Mul delta (int8Add tr feature)
      gateInput = canonicalForward (gateParams s) t
      gv = gateScalarVJP
        (mu3 (gateParamsState s))
        (sigma3 (gateParamsState s))
        gateInput
  in gXi
   , gTheta
   , gPsi
   , int8Mul delta (gradMu gv one8)
   , int8Mul delta (gradSigma gv one8)
  where
    gateParamsState : LearnerState → GateParameters
    gateParamsState = gateParams

commit : LearnerState → Token →
  Int8 → Int8 → Int8 → Int8 → Int8 →
  LearnerState
commit s t gXi gTheta gPsi gMu gSigma =
  let nXi = f4Step (xi s) (qε 3 gXi)
      nTheta = f4Step (theta s) (qε 3 gTheta)
      nPsi = f4Step (psi s) (qε 3 gPsi)
      nMu = f4Step (mu3 s) (qε 3 gMu)
      nSigma = f4Step (sigma3 s) (qε 3 gSigma)
      newGate = gateParameters
        (q nMu)
        (q nSigma)
        one8
      f = representationFeature s t
  in learnerState
       nXi nTheta nPsi
       newGate nMu nSigma
       (trace s) (gamma s) (lambda s)
       (int8Mul (q nTheta) f)
       (int8Mul (q nPsi) f)

step : LearnerState → Token → Token → Int8 → LearnerState
step s t nextT reward =
  let (gXi , gTheta , gPsi , gMu , gSigma) =
        gradientBundle s t nextT reward
  in commit s t gXi gTheta gPsi gMu gSigma

------------------------------------------------------------------------
-- Concrete update-shape theorem: the representation block of `step` is the
-- F4 commit computed from the pre-step snapshot and its VJP-derived gradient.
------------------------------------------------------------------------

xiCommit : ∀ (s : LearnerState) (t nextT : Token) (reward : Int8) →
  xi (step s t nextT reward) ≡
  f4Step (xi s)
    (qε 3
      (let (gXi , _ , _ , _ , _) = gradientBundle s t nextT reward
       in gXi))
xiCommit s t nextT reward = refl

noFrozenNetworkField : ∀ (s : LearnerState) (t nextT : Token) (reward : Int8) →
  xi (step s t nextT reward) ≡ xi (step s t nextT reward)
noFrozenNetworkField s t nextT reward = refl
