{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalLearner where

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; _+_; _*_; _∸_)
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
  ; max8
  )
open import Exotic.ERL.FullCoupled.FiniteLearner using
  ( Token
  ; Window2
  ; tokenCode
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
-- Finite dyadic scale.  exponent zero is one ULP and is the hard floor.
------------------------------------------------------------------------

twoPow : ℕ → Int8
twoPow zero = one8
twoPow (suc n) = int8Add (twoPow n) (twoPow n)

dyadicScale : Fin 8 → Int8
dyadicScale e = twoPow (toℕ e)

ellMin : Fin 8
ellMin = Fin.zero

scaleFloor : dyadicScale ellMin ≡ one8
scaleFloor = refl

------------------------------------------------------------------------
-- Three finite sigma-delta accumulators.  They are finite accumulators, not
-- an appeal to real-valued sub-ULP arithmetic.
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

f4FloorPreserved : ∀ (s : F4) → toℕ (ell (f4Step s zero8)) ≤ 7
f4FloorPreserved s = refl

f4ZeroLaw : ∀ (s : F4) →
  f4Step s zero8 ≡
  f4 (q s)
      (r1 s)
      (r2 s)
      (r3 s)
      (ell s)
f4ZeroLaw s with ell s
... | Fin.zero = refl
... | Fin.suc Fin.zero = refl
... | Fin.suc (Fin.suc Fin.zero) = refl
... | Fin.suc (Fin.suc (Fin.suc Fin.zero)) = refl
... | Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = refl
... | Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = refl
... | Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = refl
... | Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))) = refl

------------------------------------------------------------------------
-- Canonical learning state. Every learnable quantity is in the state and is
-- updated once, from one immutable snapshot.
------------------------------------------------------------------------

record LearnerState : Set where
  constructor learnerState
  field
    xi theta psi : F4
    gate : GateParameters
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
start =
  learnerState
    initialF4
    initialF4
    initialF4
    initialGate
    initialF4
    initialF4
    zero8
    one8
    one8
    zero8
    zero8

signedMagnitude : Int8 → ℕ
signedMagnitude x with toℕ (code x) ≤? 127
... | yes _ = toℕ (code x)
... | no _ = 256 ∸ toℕ (code x)

hardMax : Int8 → Int8 → Int8
hardMax x y with signedMagnitude x ≤? signedMagnitude y
... | yes _ = y
... | no _ = x

tdTarget : LearnerState → Int8 → Int8 → Int8 → Int8
tdTarget s reward nextCritic nextActor =
  int8Add reward (hardMax nextCritic nextActor)

traceStep : LearnerState → Int8 → Int8 → Int8
traceStep s feature =
  int8Add feature
    (int8Mul (gamma s) (int8Mul (lambda s) (trace s)))

tdError : LearnerState → Int8 → Int8 → Int8 → Int8 → Int8
tdError s reward feature nextCritic nextActor =
  int8Add
    (tdTarget s reward nextCritic nextActor)
    (int8OfNat (256 ∸ toℕ (code (criticOutput s))))

representationFeature : LearnerState → Token → Int8
representationFeature s t =
  int8Mul (q (xi s)) (canonicalForward (gate s) t)

gradientBundle : LearnerState → Token → Token → Int8 → Int8 × Int8 × Int8 × Int8 × Int8
gradientBundle s t nextT reward =
  let feature = representationFeature s t
      nextFeature = representationFeature s nextT
      tc = int8Mul (q (theta s)) nextFeature
      ta = int8Mul (q (psi s)) nextFeature
      nextCritic = int8Add tc (q (theta s))
      nextActor = int8Add ta (q (psi s))
      tr = traceStep s feature
      delta = tdError s reward feature nextCritic nextActor
      gTheta = int8Mul delta tr
      gPsi = int8Mul delta feature
      gXi = int8Mul delta (int8Add tr feature)
      gated = canonicalForward (gate s) t
      gv = gateScalarVJP (mu3 (gate s)) (sigma3 (gate s)) gated
      gMu = int8Mul delta (gradMu gv)
      gSigma = int8Mul delta (gradSigma gv)
  in gXi , gTheta , gPsi , gMu , gSigma

record GatePair : Set where
  constructor gatePair
  field
    mu sigma : Int8

open GatePair public

gateCommit : LearnerState → Int8 → Int8 → LearnerState
gateCommit s gm gs =
  learnerState
    (xi s)
    (theta s)
    (psi s)
    (gateParameters (q (mu3 s)) (q (sigma3 s)) (projection (gate s)))
    (mu3 s)
    (sigma3 s)
    (trace s)
    (gamma s)
    (lambda s)
    (criticOutput s)
    (actorOutput s)
  where
    projection : GateParameters → Int8
    projection g = CanonicalTransformer.projection
      (CanonicalTransformer.gate g
        (CanonicalTransformer.Pair.left (CanonicalTransformer.Pair.pair zero8 zero8)))

commit : LearnerState →
  Int8 → Int8 → Int8 → Int8 → Int8 →
  LearnerState
commit s gXi gTheta gPsi gMu gSigma =
  let nXi = f4Step (xi s) (qε 3 gXi)
      nTheta = f4Step (theta s) (qε 3 gTheta)
      nPsi = f4Step (psi s) (qε 3 gPsi)
      nMu = f4Step (mu3 s) (qε 3 gMu)
      nSigma = f4Step (sigma3 s) (qε 3 gSigma)
      newGate = gateParameters (q nMu) (q nSigma) (projection (gate s))
  in learnerState
       nXi nTheta nPsi newGate nMu nSigma
       (trace s) (gamma s) (lambda s)
       (int8Mul (q nTheta) (representationFeature s (previousToken s)))
       (int8Mul (q nPsi) (representationFeature s (previousToken s)))
  where
    previousToken : LearnerState → Token
    previousToken s = token
      zero8 zero8 zero8 zero8

    projection : GateParameters → Int8
    projection g = int8Add (mu3 g) (sigma3 g)

step : LearnerState → Token → Token → Int8 → LearnerState
step s t nextT reward =
  let (gXi , gTheta , gPsi , gMu , gSigma) = gradientBundle s t nextT reward
  in commit s gXi gTheta gPsi gMu gSigma

learningWitness : step start (token one8 zero8 one8 zero8) (token zero8 zero8 zero8 zero8) one8
  ≢ start
learningWitness ()
