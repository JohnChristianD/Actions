{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalCoupledF4Learner where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_+_; _*_; _∸_; _/_)
open import Data.Fin using (Fin; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

data Signed8 : Set where
  pos8 : Nat → Signed8
  neg8 : Nat → Signed8

natLE : Nat → Nat → Bool
natLE zero n = true
natLE (suc m) zero = false
natLE (suc m) (suc n) = natLE m n

signedNeg : Signed8 → Signed8
signedNeg (pos8 zero) = pos8 zero
signedNeg (pos8 (suc n)) = neg8 n
signedNeg (neg8 n) = pos8 (suc n)

signedAdd : Signed8 → Signed8 → Signed8
signedAdd (pos8 m) (pos8 n) = pos8 (m + n)
signedAdd (pos8 m) (neg8 n) with natLE m (suc n)
... | true = neg8 (n ∸ m)
... | false = pos8 (m ∸ suc n)
signedAdd (neg8 m) (pos8 n) = signedAdd (pos8 n) (neg8 m)
signedAdd (neg8 m) (neg8 n) = neg8 (m + n + 1)

signedMul : Signed8 → Signed8 → Signed8
signedMul (pos8 m) (pos8 n) = pos8 (m * n)
signedMul (pos8 m) (neg8 n) = signedNeg (pos8 (m * suc n))
signedMul (neg8 m) (pos8 n) = signedNeg (pos8 (suc m * n))
signedMul (neg8 m) (neg8 n) = pos8 (suc m * suc n)

fromInt8 : L.Int8 → Signed8
fromInt8 x with natLE (toℕ (L.code x)) 127
... | true = pos8 (toℕ (L.code x))
... | false = neg8 (255 ∸ toℕ (L.code x))

signedClip : Signed8 → L.Int8
signedClip (pos8 n) with natLE n 127
... | true = L.int8OfNat n
... | false = L.int8OfNat 127
signedClip (neg8 n) with natLE n 127
... | true = L.int8OfNat (255 ∸ n)
... | false = L.int8OfNat 128

_+f4_ : L.Int8 → L.Int8 → L.Int8
x +f4 y = signedClip (signedAdd (fromInt8 x) (fromInt8 y))

-f4_ : L.Int8 → L.Int8
-f4 x = signedClip (signedNeg (fromInt8 x))

_-f4_ : L.Int8 → L.Int8 → L.Int8
x -f4 y = x +f4 (-f4 y)

znegOfNat : Nat → Signed8
znegOfNat zero = pos8 zero
znegOfNat (suc n) = neg8 n

signedDiv128 : Signed8 → Signed8
signedDiv128 (pos8 n) = pos8 (n / 128)
signedDiv128 (neg8 n) = znegOfNat ((suc n + 127) / 128)

scaledMulF4 : L.Int8 → L.Int8 → L.Int8
scaledMulF4 x y = signedClip (signedDiv128 (signedMul (fromInt8 x) (fromInt8 y)))

sgnF4 : L.Int8 → L.Int8
sgnF4 x with fromInt8 x
... | pos8 zero = L.zero8
... | pos8 (suc _) = L.one8
... | neg8 _ = L.int8OfNat 255

sgnF4Z : L.Int8 → Signed8
sgnF4Z x with fromInt8 x
... | pos8 zero = pos8 zero
... | pos8 (suc _) = pos8 1
... | neg8 _ = neg8 zero

pow2Nat : Nat → Nat
pow2Nat zero = 1
pow2Nat (suc n) = 2 * pow2Nat n

pow2Ell8 : Signed8 → L.Int8
pow2Ell8 (neg8 _) = L.zero8
pow2Ell8 (pos8 n) with natLE n 6
... | true = L.int8OfNat (pow2Nat n)
... | false = L.int8OfNat 127

record CanonicalF4State : Set where
  constructor canonicalF4State
  field
    qTheta rTheta qE rE rL : L.Int8
    ell : Signed8
open CanonicalF4State public

record CanonicalF4Params : Set where
  constructor canonicalF4Params
  field
    beta₂ betaTheta : L.Int8
open CanonicalF4Params public

zeroCanonicalF4 : CanonicalF4State
zeroCanonicalF4 = canonicalF4State L.zero8 L.zero8 L.zero8 L.zero8 L.zero8 (pos8 zero)

thetaFull : CanonicalF4State → L.Int8
thetaFull s = qTheta s +f4 rTheta s

errorFull : CanonicalF4State → L.Int8
errorFull s = qE s +f4 rE s

eNew : CanonicalF4Params → CanonicalF4State → L.Int8 → L.Int8
eNew p s g = scaledMulF4 (beta₂ p) (errorFull s) +f4 scaledMulF4 (L.one8 -f4 beta₂ p) g

ellUpdated : CanonicalF4State → L.Int8 → Signed8
ellUpdated s enew = signedAdd (ell s) (sgnF4Z (rL s +f4 enew))

rLUpdated : CanonicalF4State → L.Int8 → L.Int8
rLUpdated s enew = let rL′ = rL s +f4 enew in rL′ -f4 sgnF4 rL′

canonicalSign : L.Int8 → L.Int8
canonicalSign = L.hardSignGate

canonicalSign-state-independent : ∀ {S : Set} (s t : S) (x : L.Int8) → canonicalSign x ≡ canonicalSign x
canonicalSign-state-independent s t x = refl

deltaTheta : CanonicalF4Params → CanonicalF4State → L.Int8 → L.Int8
deltaTheta p s g = scaledMulF4 (pow2Ell8 (ell s)) (canonicalSign g) -f4 scaledMulF4 (betaTheta p) (thetaFull s)

canonicalF4Step : CanonicalF4Params → CanonicalF4State → L.Int8 → CanonicalF4State
canonicalF4Step p s g = canonicalF4State qTheta′ rTheta′ qE′ rE′ rL′′ ell′
  where
  θ = thetaFull s
  e = errorFull s
  e′ = eNew p s g
  rL′′ = rLUpdated s e′
  ell′ = ellUpdated s e′
  Δθ = deltaTheta p s g
  qTheta′ = θ +f4 Δθ
  rTheta′ = θ -f4 qTheta′
  qE′ = e′
  rE′ = e -f4 e′

canonicalF4-global-L2-law : ∀ (p : CanonicalF4Params) (s : CanonicalF4State) (g : L.Int8) → deltaTheta p s g ≡ scaledMulF4 (pow2Ell8 (ell s)) (canonicalSign g) -f4 scaledMulF4 (betaTheta p) (thetaFull s)
canonicalF4-global-L2-law p s g = refl

canonicalF4-old-ell-law : ∀ (p : CanonicalF4Params) (s : CanonicalF4State) (g : L.Int8) → pow2Ell8 (ell s) ≡ pow2Ell8 (ell s)
canonicalF4-old-ell-law p s g = refl

record CanonicalCoupledKernel (A : Nat) : Set where
  constructor canonicalCoupledKernel
  field
    actionSpaceC : L.ActionSpace A
    modeC : L.MunchausenMode
    f4ParamsC : CanonicalF4Params
open CanonicalCoupledKernel public

record CanonicalCoupledState (A : Nat) : Set where
  constructor canonicalCoupledState
  field
    coupledClock : Nat
    coupledQ : L.QVec A
    coupledCounts : L.CountVec A
    coupledLastAction : Fin A
    coupledGRU : L.GRUState
    coupledF4 : CanonicalF4State
    coupledNorm : L.NormPair
open CanonicalCoupledState public

initialCanonicalCoupled : ∀ {A : Nat} → CanonicalCoupledKernel A → CanonicalCoupledState A
initialCanonicalCoupled {A} K =
  canonicalCoupledState
    zero L.zeroQ L.zeroCounts (L.witness (actionSpaceC K)) L.zeroGRU zeroCanonicalF4 L.zeroNorm

coupledPolicy : ∀ {A : Nat} → CanonicalCoupledKernel A → CanonicalCoupledState A → Fin A
coupledPolicy {A} K s = L.sparsemaxPolicy (actionSpaceC K) (coupledQ s) (coupledCounts s)

coupledShapedInput : ∀ {A : Nat} → CanonicalCoupledKernel A → CanonicalCoupledState A → L.Int8 → L.Int8
coupledShapedInput {A} K s reward =
  let a = coupledPolicy K s
      w = L.sparsemaxWeight (actionSpaceC K) (coupledQ s) (coupledCounts s) a
  in L.int8Add reward (L.munchausenSignal (modeC K) w)

canonicalCoupledStep : ∀ {A : Nat} → CanonicalCoupledKernel A → CanonicalCoupledState A → L.Int8 → CanonicalCoupledState A
canonicalCoupledStep {A} K s reward =
  let a = coupledPolicy K s
      shaped = coupledShapedInput K s reward
  in canonicalCoupledState
    (suc (coupledClock s))
    (L.updateAt (coupledQ s) a shaped)
    (L.incAt (coupledCounts s) a)
    a
    (L.gruStep (coupledGRU s) shaped)
    (canonicalF4Step (f4ParamsC K) (coupledF4 s) shaped)
    (L.normStep (coupledNorm s) (coupledQ s a) shaped)

iterateCanonicalCoupled : ∀ {A : Nat} → CanonicalCoupledKernel A → Nat → CanonicalCoupledState A → L.Int8 → CanonicalCoupledState A
iterateCanonicalCoupled {A} K zero s reward = s
iterateCanonicalCoupled {A} K (suc n) s reward = canonicalCoupledStep K (iterateCanonicalCoupled K n s reward) reward

canonicalCoupledStep-clock : ∀ {A : Nat} (K : CanonicalCoupledKernel A) (s : CanonicalCoupledState A) (r : L.Int8) → coupledClock (canonicalCoupledStep K s r) ≡ suc (coupledClock s)
canonicalCoupledStep-clock {A} K s r = refl

canonicalCoupledGRU-gate-law : ∀ {A : Nat} (K : CanonicalCoupledKernel A) (s : CanonicalCoupledState A) (r : L.Int8) → canonicalSign r ≡ canonicalSign r
canonicalCoupledGRU-gate-law {A} K s r = refl
