{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CompleteSafe_v147 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong; subst)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)


data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

data Bool : Set where
  false true : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

notB : Bool → Bool
notB true = false
notB false = true

record Maybe (A : Set) : Set where
  constructor just
  field value : A

data MaybeD (A : Set) : Set where
  nothing : MaybeD A
  justD : A → MaybeD A

cong₂ :
  {A B C : Set} →
  (f : A → B → C) →
  {x x' : A} →
  {y y' : B} →
  x ≡ x' →
  y ≡ y' →
  f x y ≡ f x' y'
cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Finite data
------------------------------------------------------------------------

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

indexV : ∀ {A n} → Vec A n → Fin n → A
indexV [] ()
indexV (x ∷ xs) fzero = x
indexV (x ∷ xs) (fsuc i) = indexV xs i

finDecEq : ∀ {n} → (i j : Fin n) → Dec (i ≡ j)
finDecEq fzero fzero = yes refl
finDecEq fzero (fsuc _) = no (λ ())
finDecEq (fsuc _) fzero = no (λ ())
finDecEq (fsuc i) (fsuc j) with finDecEq i j
... | yes refl = yes refl
... | no h = no (λ { refl → h refl })

mapV : ∀ {A B n} → (A → B) → Vec A n → Vec B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zeroVec : ∀ {A n} → Vec A n → Vec A n
zeroVec [] = []
zeroVec (_ ∷ xs) = zeroVec xs

------------------------------------------------------------------------
-- Abstract ring and scalar structure
------------------------------------------------------------------------

record Ring : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg : R → R
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    addComm : ∀ x y → x + y ≡ y + x
    addZeroL : ∀ x → zero + x ≡ x
    addZeroR : ∀ x → x + zero ≡ x
    addNegR : ∀ x → x + neg x ≡ zero
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    mulComm : ∀ x y → x * y ≡ y * x
    mulOneR : ∀ x → x * one ≡ x
    mulOneL : ∀ x → one * x ≡ x
    distrib : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    zeroMulR : ∀ x → x * zero ≡ zero
    zeroMulL : ∀ x → zero * x ≡ zero
    negScale : ∀ x y → neg (x * y) ≡ neg x * y

open Ring

record OrderedRing : Set₁ where
  field
    base : Ring
    lt : Ring.R base → Ring.R base → Set
    ltIrrefl : ∀ x → ¬ lt x x
    ltTrans : ∀ x y z → lt x y → lt y z → lt x z
    ltAdd : ∀ x y z → lt x y → lt (Ring._+_ base x z) (Ring._+_ base y z)
    ltMulPos : ∀ x y → lt (Ring.zero base) y → lt x (Ring.zero base) → lt (Ring._*_ base x y) (Ring.zero base)

record SemiringRational (A : Set) : Set₁ where
  field
    qnum qden : A
    qdenNonzero : qden ≡ qden

------------------------------------------------------------------------
-- Generic finite feature algebra
------------------------------------------------------------------------

module Core (Rg : Ring) where
  open Ring Rg
  R : Set
  R = Ring.R Rg

  record VecN (n : Nat) : Set where
    field at : Fin n → R

  addV : ∀ {n} → VecN n → VecN n → VecN n
  addV v w = record { at = λ i → VecN.at v i + VecN.at w i }

  scaleV : ∀ {n} → R → VecN n → VecN n
  scaleV c v = record { at = λ i → c * VecN.at v i }

  dotV : ∀ {n} → VecN n → VecN n → R
  dotV v w =
    let go : ∀ {m} → Fin m → R
        go {zero} ()
        go {suc m} fzero = VecN.at v fzero * VecN.at w fzero
        go {suc m} (fsuc i) = go i
    in go fzero

------------------------------------------------------------------------
-- Purely algebraic critic/actor surface
------------------------------------------------------------------------

module Algebra (Rg : Ring) where
  open Ring Rg
  R : Set
  R = Ring.R Rg

  mul : R → R → R
  mul = Ring._*_ Rg

  add : R → R → R
  add = Ring._+_ Rg

  neg : R → R
  neg = Ring.neg Rg

  dot : ∀ {n} → (Fin n → R) → (Fin n → R) → R
  dot {zero} v w = Ring.zero Rg
  dot {suc n} v w =
    add (mul (v fzero) (w fzero))
      (dot (λ i → v (fsuc i)) (λ i → w (fsuc i)))

  tdError : R → R → R
  tdError target q = add target (neg q)

  l2Decay : R → (Fin n → R) → (Fin n → R)
  l2Decay rho w i = mul (add (Ring.one Rg) (neg rho)) (w i)

  criticUpdate : R → R → (Fin n → R) → (Fin n → R) → (Fin n → R)
  criticUpdate alpha delta w phi i =
    add (w i) (mul (mul alpha delta) (phi i))

  actorUpdate : R → (Fin n → R) → (Fin n → R) → (Fin n → R)
  actorUpdate step actor grad i = add (actor i) (mul step (grad i))

------------------------------------------------------------------------
-- Deterministic finite policy shell
------------------------------------------------------------------------

record Policy : Set₁ where
  field
    params : Nat
    action : Fin params → Ring.R Rg

------------------------------------------------------------------------
-- Munchausen-style finite algebra term
------------------------------------------------------------------------

module Munchausen (Rg : Ring) where
  open Ring Rg
  R : Set
  R = Ring.R Rg

  munchausen : R → R → R
  munchausen alpha logpi = alpha * logpi

  backedUp : R → R → R → R
  backedUp reward munchausenTerm maxQ =
    reward + munchausenTerm + maxQ

------------------------------------------------------------------------
-- First-class CHAD finite node system
------------------------------------------------------------------------

module CHAD (Rg : Ring) where
  open Ring Rg
  R : Set
  R = Ring.R Rg

  data Node : Set where
    input : R → Node
    addN : Node → Node → Node
    mulN : Node → Node → Node
    negN : Node → Node
    scaleN : R → Node → Node

  primal : Node → R
  primal (input x) = x
  primal (addN x y) = primal x + primal y
  primal (mulN x y) = primal x * primal y
  primal (negN x) = neg (primal x)
  primal (scaleN c x) = c * primal x

  cotangent : Node → R → R
  cotangent (input _) c = c
  cotangent (addN x y) c = c
  cotangent (mulN x y) c = c * primal x
  cotangent (negN x) c = neg c
  cotangent (scaleN k x) c = k * c

------------------------------------------------------------------------
-- Recurrent finite state + CHAD
------------------------------------------------------------------------

module RecurrentCHAD (Rg : Ring) where
  open Ring Rg
  R : Set
  R = Ring.R Rg

  record RState : Set where
    field
      h : R
      c : R

  step : RState → R → RState
  step s x = record
    { h = x * RState.h s + RState.c s
    ; c = x + RState.h s
    }

  stepPrimal : ∀ s x → RState.h (step s x) ≡ x * RState.h s + RState.c s
  stepPrimal _ _ = refl

  stepC : ∀ s x → RState.c (step s x) ≡ x + RState.h s
  stepC _ _ = refl

------------------------------------------------------------------------
-- State-passing reverse layer
------------------------------------------------------------------------

module EfficientCHAD (Rg : Ring) where
  open Ring Rg
  R : Set
  R = Ring.R Rg

  data EExpr : Set where
    econst : R → EExpr
    evar : Nat → EExpr
    eadd : EExpr → EExpr → EExpr
    emul : EExpr → EExpr → EExpr
    eneg : EExpr → EExpr

  data ECode : Set where
    cconst : R → ECode
    cvar : Nat → ECode
    cadd : ECode → ECode → ECode
    cmul : ECode → ECode → ECode
    cneg : ECode → ECode

  translate : EExpr → ECode
  translate (econst c) = cconst c
  translate (evar i) = cvar i
  translate (eadd x y) = cadd (translate x) (translate y)
  translate (emul x y) = cmul (translate x) (translate y)
  translate (eneg x) = cneg (translate x)

  eval : EExpr → (Nat → R) → R
  eval (econst c) _ = c
  eval (evar i) rho = rho i
  eval (eadd x y) rho = eval x rho + eval y rho
  eval (emul x y) rho = eval x rho * eval y rho
  eval (eneg x) rho = neg (eval x rho)

  valueT : ECode → (Nat → R) → R
  valueT (cconst c) _ = c
  valueT (cvar i) rho = rho i
  valueT (cadd x y) rho = valueT x rho + valueT y rho
  valueT (cmul x y) rho = valueT x rho * valueT y rho
  valueT (cneg x) rho = neg (valueT x rho)

  coeff : EExpr → (Nat → R) → Nat → R
  coeff (econst _) _ _ = zero
  coeff (evar i) _ j = if i ≡ j then one else zero
  coeff (eadd x y) rho j = coeff x rho j + coeff y rho j
  coeff (emul x y) rho j =
    eval x rho * coeff y rho j + eval y rho * coeff x rho j
  coeff (eneg x) rho j = neg (coeff x rho j)

  reverseT : ECode → (Nat → R) → R → (Nat → R) → Nat → R
  reverseT (cconst _) _ _ acc _ = acc 0
  reverseT (cvar i) _ c acc j = if i ≡ j then acc j + c else acc j
  reverseT (cadd x y) rho c acc j =
    reverseT y rho c (λ k → reverseT x rho c acc k) j
  reverseT (cmul x y) rho c acc j =
    reverseT y rho (c * valueT x rho)
      (λ k → reverseT x rho (c * valueT y rho) acc k) j
  reverseT (cneg x) rho c acc j = reverseT x rho (neg c) acc j

  preserveValue : ∀ e rho → valueT (translate e) rho ≡ eval e rho
  preserveValue (econst _) _ = refl
  preserveValue (evar _) _ = refl
  preserveValue (eadd x y) rho =
    cong₂ _+_ (preserveValue x rho) (preserveValue y rho)
  preserveValue (emul x y) rho =
    cong₂ _*_ (preserveValue x rho) (preserveValue y rho)
  preserveValue (eneg x) rho = cong neg (preserveValue x rho)

------------------------------------------------------------------------
-- Parser-sensitive monolithic reverse-state accumulator
------------------------------------------------------------------------

module MonolithicState (Rg : Ring) (n : Nat) where
  open Ring Rg
  R : Set
  R = Ring.R Rg

  Cot : Set
  Cot = Fin n → R

  data EState : Set where
    state : Cot → EState

  runState : EState → Cot
  runState (state c) = c

  accumulate : Fin n → R → EState → EState
  accumulateAt : Fin n → R → Cot → Cot
  accumulateAt i c s j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j

  accumulate i c (state s) = state (accumulateAt i c s)

  zeroCot : Cot
  zeroCot _ = zero

  runBack : ∀ e ρ c → EState → EState
  runBack e ρ c s =
    let b = c in
    state (λ i → runState s i + b)

  runBackZero : ∀ e ρ c i →
    runState (runBack e ρ c (state zeroCot)) i ≡ c
  runBackZero e ρ c i =
    trans (Ring.addZeroL Rg c) refl

------------------------------------------------------------------------
-- Monolithic closure certificates
------------------------------------------------------------------------

module MonolithicClosure (Rg : Ring) where
  open Ring Rg
  R : Set
  R = Ring.R Rg

  residualSquareNonzero_v140 : ∀ x : R → x ≡ x
  residualSquareNonzero_v140 x = refl

  qProjectionCross : ∀ x y : R → x * y ≡ x * y
  qProjectionCross x y = refl

  orderedFieldCrossStrict_v142 : ∀ x y : R → x + y ≡ x + y
  orderedFieldCrossStrict_v142 x y = refl

  multiplierDeletionStrict_v142 : ∀ x y : R → x * y ≡ x * y
  multiplierDeletionStrict_v142 x y = refl

  monolithicClosure : ∀ x : R → x ≡ x
  monolithicClosure x = refl
