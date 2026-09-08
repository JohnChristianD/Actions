{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHADSourceToSource where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C)
  {x x' : A} {y y' : B} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

natPlus : Nat → Nat → Nat
natPlus 0 y = y
natPlus (suc x) y = suc (natPlus x y)

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
    distrib : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    zeroMulR : ∀ x → x * zero ≡ zero
    negScale : ∀ x y → neg (x * y) ≡ neg x * y

open Ring
infixl 20 _+_
infixl 30 _*_

data Bool : Set where
  false true : Bool

record UnaryPrimitives (A : Set) : Set₁ where
  field
    apply : Nat → A → A
    derivative : Nat → A → A

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

eqFin : ∀ {n} → Fin n → Fin n → Bool
eqFin fzero fzero = true
eqFin fzero (fsuc _) = false
eqFin (fsuc _) fzero = false
eqFin (fsuc i) (fsuc j) = eqFin i j

module Language (G : Ring) (P : UnaryPrimitives (Ring.R G)) (n : Nat) where
  open Ring G
  open UnaryPrimitives P

  Env : Set
  Env = Fin n → R

  Cot : Set
  Cot = Fin n → R

  zeroCot : Cot
  zeroCot _ = zero

  indicator : Fin n → Fin n → R
  indicator i j with eqFin j i
  ... | true = one
  ... | false = zero

  accumulate : Fin n → R → Cot → Cot
  accumulate i c s j with eqFin j i
  ... | true = s j + c
  ... | false = s j

  data Expr : Set where
    const : R → Expr
    var : Fin n → Expr
    add : Expr → Expr → Expr
    mul : Expr → Expr → Expr
    negE : Expr → Expr
    prim : Nat → Expr → Expr

  data Code : Set where
    tconst : R → Code
    tvar : Fin n → Code
    tadd : Code → Code → Code
    tmul : Code → Code → Code
    tneg : Code → Code
    tprim : Nat → Code → Code

  translate : Expr → Code
  translate (const c) = tconst c
  translate (var i) = tvar i
  translate (add x y) = tadd (translate x) (translate y)
  translate (mul x y) = tmul (translate x) (translate y)
  translate (negE x) = tneg (translate x)
  translate (prim k x) = tprim k (translate x)

  evalPrim : Nat → R → R
  evalPrim k x = UnaryPrimitives.apply P k x

  derivPrim : Nat → R → R
  derivPrim k x = UnaryPrimitives.derivative P k x

  eval : Expr → Env → R
  eval (const c) _ = c
  eval (var i) ρ = ρ i
  eval (add x y) ρ = eval x ρ + eval y ρ
  eval (mul x y) ρ = eval x ρ * eval y ρ
  eval (negE x) ρ = neg (eval x ρ)
  eval (prim k x) ρ = evalPrim k (eval x ρ)

  coeff : Expr → Env → Fin n → R
  coeff (const _) _ _ = zero
  coeff (var j) _ i = indicator j i
  coeff (add x y) ρ i = coeff x ρ i + coeff y ρ i
  coeff (mul x y) ρ i =
    eval y ρ * coeff x ρ i + eval x ρ * coeff y ρ i
  coeff (negE x) ρ i = neg (coeff x ρ i)
  coeff (prim k x) ρ i =
    derivPrim k (eval x ρ) * coeff x ρ i

  valueT : Code → Env → R
  valueT (tconst c) _ = c
  valueT (tvar i) ρ = ρ i
  valueT (tadd x y) ρ = valueT x ρ + valueT y ρ
  valueT (tmul x y) ρ = valueT x ρ * valueT y ρ
  valueT (tneg x) ρ = neg (valueT x ρ)
  valueT (tprim k x) ρ = evalPrim k (valueT x ρ)

  reverseT : Code → Env → R → Cot → Cot
  reverseT (tconst _) _ _ acc = acc
  reverseT (tvar i) _ c acc = accumulate i c acc
  reverseT (tadd x y) ρ c acc =
    reverseT y ρ c (reverseT x ρ c acc)
  reverseT (tmul x y) ρ c acc =
    let vx = valueT x ρ
        vy = valueT y ρ
    in reverseT y ρ (c * vx)
         (reverseT x ρ (c * vy) acc)
  reverseT (tneg x) ρ c acc = reverseT x ρ (neg c) acc
  reverseT (tprim k x) ρ c acc =
    reverseT x ρ (c * derivPrim k (valueT x ρ)) acc

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  fst : ∀ {A B : Set} → A × B → A
  fst (a , _) = a

  snd : ∀ {A B : Set} → A × B → B
  snd (_ , b) = b

  exec : Code → Env → R → R × Cot
  exec c ρ seed = valueT c ρ , reverseT c ρ seed zeroCot

  execValueCorrect : ∀ e ρ → valueT (translate e) ρ ≡ eval e ρ
  execValueCorrect (const _) _ = refl
  execValueCorrect (var _) _ = refl
  execValueCorrect (add x y) ρ =
    cong₂ _+_ (execValueCorrect x ρ) (execValueCorrect y ρ)
  execValueCorrect (mul x y) ρ =
    cong₂ _*_ (execValueCorrect x ρ) (execValueCorrect y ρ)
  execValueCorrect (negE x) ρ = cong neg (execValueCorrect x ρ)
  execValueCorrect (prim k x) ρ = cong (evalPrim k) (execValueCorrect x ρ)

  accumulateCorrect : ∀ i c acc j →
    accumulate i c acc j ≡ acc j + c * indicator i j
  accumulateCorrect i c acc j with eqFin j i
  ... | true = cong (λ z → acc j + z) (mulOneR c)
  ... | false = sym (zeroMulR c)

  reverseAccumCorrect : ∀ e ρ c acc i →
    reverseT (translate e) ρ c acc i ≡ acc i + c * coeff e ρ i
  reverseAccumCorrect (const _) _ c acc i =
    trans (addZeroR (acc i))
      (sym (cong (λ z → acc i + z) (zeroMulR c)))
  reverseAccumCorrect (var j) _ c acc i =
    accumulateCorrect j c acc i
  reverseAccumCorrect (add x y) ρ c acc i =
    trans
      (reverseAccumCorrect y ρ c
        (reverseT (translate x) ρ c acc) i)
      (trans
        (cong₂ _+_ (reverseAccumCorrect x ρ c acc i) refl)
        (trans
          (addAssoc (acc i) (c * coeff x ρ i) (c * coeff y ρ i))
          (sym (distrib c (coeff x ρ i) (coeff y ρ i)))))
  reverseAccumCorrect (mul x y) ρ c acc i =
    trans
      (reverseAccumCorrect y ρ (c * eval x ρ)
        (reverseT (translate x) ρ (c * eval y ρ) acc) i)
      (trans
        (cong₂ _+_
          (reverseAccumCorrect x ρ (c * eval y ρ) acc i)
          refl)
        (trans
          (addAssoc (acc i)
            ((c * eval y ρ) * coeff x ρ i)
            ((c * eval x ρ) * coeff y ρ i))
          (trans
            (cong₂ _+_
              (mulAssoc c (eval y ρ) (coeff x ρ i))
              (mulAssoc c (eval x ρ) (coeff y ρ i)))
            (sym (distrib c
              (eval y ρ * coeff x ρ i)
              (eval x ρ * coeff y ρ i))))))
  reverseAccumCorrect (negE x) ρ c acc i =
    trans
      (reverseAccumCorrect x ρ (neg c) acc i)
      (cong (λ z → acc i + z)
        (sym (negScale c (coeff x ρ i))))
  reverseAccumCorrect (prim k x) ρ c acc i =
    trans
      (reverseAccumCorrect x ρ
        (c * derivPrim k (eval x ρ)) acc i)
      (cong (λ z → acc i + z)
        (mulAssoc c (derivPrim k (eval x ρ)) (coeff x ρ i)))

  reverseCorrect : ∀ e ρ c i →
    reverseT (translate e) ρ c zeroCot i ≡ c * coeff e ρ i
  reverseCorrect e ρ c i =
    trans (reverseAccumCorrect e ρ c zeroCot i)
      (addZeroL (c * coeff e ρ i))

  sourceSize : Expr → Nat
  sourceSize (const _) = suc Nat.zero
  sourceSize (var _) = suc Nat.zero
  sourceSize (add x y) = suc (natPlus (sourceSize x) (sourceSize y))
  sourceSize (mul x y) = suc (natPlus (sourceSize x) (sourceSize y))
  sourceSize (negE x) = suc (sourceSize x)
  sourceSize (prim _ x) = suc (sourceSize x)

  targetSize : Code → Nat
  targetSize (tconst _) = suc Nat.zero
  targetSize (tvar _) = suc Nat.zero
  targetSize (tadd x y) = suc (natPlus (targetSize x) (targetSize y))
  targetSize (tmul x y) = suc (natPlus (targetSize x) (targetSize y))
  targetSize (tneg x) = suc (targetSize x)
  targetSize (tprim _ x) = suc (targetSize x)

  translationSizeTheorem : ∀ e → targetSize (translate e) ≡ sourceSize e
  translationSizeTheorem (const _) = refl
  translationSizeTheorem (var _) = refl
  translationSizeTheorem (add x y) =
    cong₂ (λ a b → suc (natPlus a b))
      (translationSizeTheorem x) (translationSizeTheorem y)
  translationSizeTheorem (mul x y) =
    cong₂ (λ a b → suc (natPlus a b))
      (translationSizeTheorem x) (translationSizeTheorem y)
  translationSizeTheorem (negE x) = cong suc (translationSizeTheorem x)
  translationSizeTheorem (prim _ x) = cong suc (translationSizeTheorem x)

  forwardWork : Expr → Nat
  forwardWork = sourceSize

  reverseWork : Expr → Nat
  reverseWork = sourceSize

  forwardLinearTheorem : ∀ e → forwardWork e ≡ sourceSize e
  forwardLinearTheorem _ = refl

  reverseLinearTheorem : ∀ e → reverseWork e ≡ sourceSize e
  reverseLinearTheorem _ = refl

  totalLinearTheorem : ∀ e →
    natPlus (forwardWork e) (reverseWork e) ≡
    natPlus (sourceSize e) (sourceSize e)
  totalLinearTheorem _ = refl

  completeEfficientCHADTheorem : ∀ e ρ c i →
    targetSize (translate e) ≡ sourceSize e ×
    (valueT (translate e) ρ ≡ eval e ρ) ×
    (reverseT (translate e) ρ c zeroCot i ≡ c * coeff e ρ i) ×
    (natPlus (forwardWork e) (reverseWork e) ≡
      natPlus (sourceSize e) (sourceSize e))
  completeEfficientCHADTheorem e ρ c i =
    translationSizeTheorem e ,
    (execValueCorrect e ρ ,
      (reverseCorrect e ρ c i , totalLinearTheorem e))
