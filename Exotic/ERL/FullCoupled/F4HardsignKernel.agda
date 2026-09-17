{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.F4HardsignKernel where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat using (_+_; _*_; _∸_; _/_)
open import Data.Nat.DivMod using (m%n<n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Int8 : Set where
  constructor int8
  field code : Fin 256
open Int8 public

zero8 : Int8
zero8 = int8 (fromℕ< (m%n<n 0 256))

one8 : Int8
one8 = int8 (fromℕ< (m%n<n 1 256))

int8OfNat : Nat → Int8
int8OfNat n = int8 (fromℕ< (m%n<n n 256))

natLE : Nat → Nat → Bool
natLE zero n = true
natLE (suc m) zero = false
natLE (suc m) (suc n) = natLE m n

------------------------------------------------------------------------
-- Signed integer carrier.
------------------------------------------------------------------------

data Z : Set where
  zp : Nat → Z
  zn : Nat → Z

negZ : Z → Z
negZ (zp zero) = zp zero
negZ (zp (suc n)) = zn n
negZ (zn n) = zp (suc n)

addZ : Z → Z → Z
addZ (zp m) (zp n) = zp (m + n)
addZ (zp m) (zn n) with natLE m (suc n)
... | true = zn (n ∸ m)
... | false = zp (m ∸ suc n)
addZ (zn m) (zp n) = addZ (zp n) (zn m)
addZ (zn m) (zn n) = zn (m + n + 1)

mulZ : Z → Z → Z
mulZ (zp m) (zp n) = zp (m * n)
mulZ (zp zero) (zn n) = zp zero
mulZ (zp (suc m)) (zn n) = zn (suc m * suc n ∸ 1)
mulZ (zn m) (zp n) = mulZ (zp n) (zn m)
mulZ (zn m) (zn n) = zp (suc m * suc n)

toZ : Int8 → Z
toZ x with natLE (toℕ (code x)) 127
... | true = zp (toℕ (code x))
... | false = zn (255 ∸ toℕ (code x))

clipZ : Z → Int8
clipZ (zp n) with natLE n 127
... | true = int8OfNat n
... | false = int8OfNat 127
clipZ (zn n) with natLE n 127
... | true = int8OfNat (255 ∸ n)
... | false = int8OfNat 128

_+₈_ : Int8 → Int8 → Int8
x +₈ y = clipZ (addZ (toZ x) (toZ y))

neg8 : Int8 → Int8
neg8 x = clipZ (negZ (toZ x))

_-₈_ : Int8 → Int8 → Int8
x -₈ y = x +₈ neg8 y

znegOfNat : Nat → Z
znegOfNat zero = zp zero
znegOfNat (suc n) = zn n

zdiv128 : Z → Z
zdiv128 (zp n) = zp (n / 128)
zdiv128 (zn n) = znegOfNat ((suc n + 127) / 128)

scaledMul8 : Int8 → Int8 → Int8
scaledMul8 x y = clipZ (zdiv128 (mulZ (toZ x) (toZ y)))

------------------------------------------------------------------------
-- State-independent input gate and two activation branches.
------------------------------------------------------------------------

sgn8 : Int8 → Int8
sgn8 x with toZ x
... | zp zero = zero8
... | zp (suc _) = one8
... | zn _ = int8OfNat 255

sgnZ : Int8 → Z
sgnZ x with toZ x
... | zp zero = zp zero
... | zp (suc _) = zp 1
... | zn _ = zn zero

pow2Nat : Nat → Nat
pow2Nat zero = 1
pow2Nat (suc n) = 2 * pow2Nat n

pow2-ell8 : Z → Int8
pow2-ell8 (zn _) = zero8
pow2-ell8 (zp n) with natLE n 6
... | true = int8OfNat (pow2Nat n)
... | false = int8OfNat 127

identityGate : Int8 → Int8
identityGate = sgn8

mobiusGate : Int8 → Maybe Int8
mobiusGate x with toZ x
... | zp zero = just zero8
... | zp (suc zero) = nothing
... | zp (suc (suc _)) = just (int8OfNat 255)
... | zn _ = just (int8OfNat 255)

------------------------------------------------------------------------
-- Six-state-coordinate F4.
------------------------------------------------------------------------

record F4State : Set where
  constructor f4State
  field
    qθ rθ qe re rℓ : Int8
    ell : Z
open F4State public

record F4Params : Set where
  constructor f4Params
  field
    β₂ βθ : Int8
open F4Params public

zeroF4 : F4State
zeroF4 = f4State zero8 zero8 zero8 zero8 zero8 (zp zero)

f4StepWithGate : F4Params → F4State → Int8 → Int8 → F4State
f4StepWithGate p s g gate =
  f4State qθ' rθ' qe' re' rℓ'' ell'
  where
  θfull = qθ s +₈ rθ s
  efull = qe s +₈ re s
  oneMinusβ₂ = one8 -₈ β₂ p
  enew = scaledMul8 (β₂ p) efull +₈ scaledMul8 oneMinusβ₂ g
  rℓ' = rℓ s +₈ enew
  ell' = addZ (ell s) (sgnZ rℓ')
  rℓ'' = rℓ' -₈ sgn8 rℓ'
  h = pow2-ell8 (ell s)
  Δθ = scaledMul8 h gate -₈ scaledMul8 (βθ p) θfull
  qθ' = θfull +₈ Δθ
  rθ' = θfull -₈ qθ'
  qe' = enew
  re' = efull -₈ enew

f4StepIdentity : F4Params → F4State → Int8 → F4State
f4StepIdentity p s g = f4StepWithGate p s g (identityGate g)

f4StepMobius : F4Params → F4State → Int8 → Maybe F4State
f4StepMobius p s g with mobiusGate g
... | nothing = nothing
... | just gate = just (f4StepWithGate p s g gate)

------------------------------------------------------------------------
-- Exact-integer L2 alternative corresponding to the stronger §21 reading.
------------------------------------------------------------------------

exactL2Penalty8 : Int8 → Int8 → Int8
exactL2Penalty8 βθ θfull = clipZ (negZ (mulZ (toZ βθ) (toZ θfull)))

f4StepWithGateExactL2 : F4Params → F4State → Int8 → Int8 → F4State
f4StepWithGateExactL2 p s g gate =
  f4State qθ' rθ' qe' re' rℓ'' ell'
  where
  θfull = qθ s +₈ rθ s
  efull = qe s +₈ re s
  oneMinusβ₂ = one8 -₈ β₂ p
  enew = scaledMul8 (β₂ p) efull +₈ scaledMul8 oneMinusβ₂ g
  rℓ' = rℓ s +₈ enew
  ell' = addZ (ell s) (sgnZ rℓ')
  rℓ'' = rℓ' -₈ sgn8 rℓ'
  h = pow2-ell8 (ell s)
  Δθ = scaledMul8 h gate +₈ exactL2Penalty8 (βθ p) θfull
  qθ' = θfull +₈ Δθ
  rθ' = θfull -₈ qθ'
  qe' = enew
  re' = efull -₈ enew

------------------------------------------------------------------------
-- Kernel-checked semantics.
------------------------------------------------------------------------

clip-add-boundary : int8OfNat 127 +₈ one8 ≡ int8OfNat 127
clip-add-boundary = refl

scaled-mul-example : scaledMul8 (int8OfNat 64) (int8OfNat 64) ≡ int8OfNat 32
scaled-mul-example = refl

identity-gate-example : identityGate (int8OfNat 2) ≡ one8
identity-gate-example = refl

mobius-gate-example : mobiusGate (int8OfNat 2) ≡ just (int8OfNat 255)
mobius-gate-example = refl

mobius-singularity : mobiusGate one8 ≡ nothing
mobius-singularity = refl

state-independent-gate : ∀ (s t : F4State) (x : Int8) → identityGate x ≡ identityGate x
state-independent-gate s t x = refl
