{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.EfficientCHADSourceToSource where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

record Ring : Set₁ where
  field
    R : Set
    zero : R
    one : R
    add : R → R → R
    mul : R → R → R
    neg : R → R
    add-zeroʳ : ∀ x → add x zero ≡ x
    mul-oneʳ : ∀ x → mul x one ≡ x

module Over (A : Ring) where

  open Ring A

  addR : R → R → R
  addR = add

  mulR : R → R → R
  mulR = mul

  negR : R → R
  negR = neg

  data Bool : Set where
    false : Bool
    true : Bool

  data Fin : Nat → Set where
    fzero : ∀ {n} → Fin (suc n)
    fsuc : ∀ {n} → Fin n → Fin (suc n)

  eqFin : ∀ {n} → Fin n → Fin n → Bool
  eqFin fzero fzero = true
  eqFin fzero (fsuc _) = false
  eqFin (fsuc _) fzero = false
  eqFin (fsuc i) (fsuc j) = eqFin i j

  record UnaryPrimitives : Set where
    field
      prim : R → R
      dprim : R → R

  module Language (P : UnaryPrimitives) where

    open UnaryPrimitives P

    data Env : Nat → Set where
      envNil : Env zero
      envCons : ∀ {n} → R → Env n → Env (suc n)

    lookup : ∀ {n} → Fin n → Env n → R
    lookup fzero (envCons x _) = x
    lookup (fsuc i) (envCons _ ρ) = lookup i ρ

    data Cot : Nat → Set where
      cotNil : Cot zero
      cotCons : ∀ {n} → R → Cot n → Cot (suc n)

    zeroCot : ∀ {n} → Cot n
    zeroCot {zero} = cotNil
    zeroCot {suc n} = cotCons zero zeroCot

    indicator : ∀ {n} → Fin n → R → Cot n
    indicator fzero c = cotCons c zeroCot
    indicator (fsuc i) c = cotCons zero (indicator i c)

    accumulate : ∀ {n} → Cot n → Cot n → Cot n
    accumulate cotNil cotNil = cotNil
    accumulate (cotCons x xs) (cotCons y ys) = cotCons (addR x y) (accumulate xs ys)

    data Expr : Nat → Set where
      const : ∀ {n} → R → Expr n
      var : ∀ {n} → Fin n → Expr n
      addE : ∀ {n} → Expr n → Expr n → Expr n
      mulE : ∀ {n} → Expr n → Expr n → Expr n
      negE : ∀ {n} → Expr n → Expr n
      prim : ∀ {n} → Expr n → Expr n

    data Code : Nat → Set where
      tconst : ∀ {n} → R → Code n
      tvar : ∀ {n} → Fin n → Code n
      tadd : ∀ {n} → Code n → Code n → Code n
      tmul : ∀ {n} → Code n → Code n → Code n
      tneg : ∀ {n} → Code n → Code n
      tprim : ∀ {n} → Code n → Code n

    translate : ∀ {n} → Expr n → Code n
    translate (const x) = tconst x
    translate (var i) = tvar i
    translate (addE e₁ e₂) = tadd (translate e₁) (translate e₂)
    translate (mulE e₁ e₂) = tmul (translate e₁) (translate e₂)
    translate (negE e) = tneg (translate e)
    translate (prim e) = tprim (translate e)

    evalPrim : R → R
    evalPrim = prim

    derivPrim : R → R
    derivPrim = dprim

    eval : ∀ {n} → Expr n → Env n → R
    eval (const x) ρ = x
    eval (var i) ρ = lookup i ρ
    eval (addE e₁ e₂) ρ = addR (eval e₁ ρ) (eval e₂ ρ)
    eval (mulE e₁ e₂) ρ = mulR (eval e₁ ρ) (eval e₂ ρ)
    eval (negE e) ρ = negR (eval e ρ)
    eval (prim e) ρ = evalPrim (eval e ρ)

    coeff : ∀ {n} → Expr n → Env n → Fin n → R
    coeff (const _) ρ i = zero
    coeff (var j) ρ i with eqFin j i
    ... | false = zero
    ... | true = one
    coeff (addE e₁ e₂) ρ i = addR (coeff e₁ ρ i) (coeff e₂ ρ i)
    coeff (mulE e₁ e₂) ρ i =
      addR
        (mulR (coeff e₁ ρ i) (eval e₂ ρ))
        (mulR (eval e₁ ρ) (coeff e₂ ρ i))
    coeff (negE e) ρ i = negR (coeff e ρ i)
    coeff (prim e) ρ i = mulR (derivPrim (eval e ρ)) (coeff e ρ i)

    valueT : ∀ {n} → Code n → Env n → R
    valueT (tconst x) ρ = x
    valueT (tvar i) ρ = lookup i ρ
    valueT (tadd e₁ e₂) ρ = addR (valueT e₁ ρ) (valueT e₂ ρ)
    valueT (tmul e₁ e₂) ρ = mulR (valueT e₁ ρ) (valueT e₂ ρ)
    valueT (tneg e) ρ = negR (valueT e ρ)
    valueT (tprim e) ρ = evalPrim (valueT e ρ)

    data _×_ (A B : Set) : Set where
      _,_ : A → B → A × B

    exec : ∀ {n} → Code n → Env n → R × Cot n
    exec (tconst x) ρ = x , zeroCot
    exec (tvar i) ρ = lookup i ρ , indicator i one
    exec (tadd e₁ e₂) ρ with exec e₁ ρ
    ... | v₁ , c₁ with exec e₂ ρ
    ... | v₂ , c₂ = addR v₁ v₂ , accumulate c₁ c₂
    exec (tmul e₁ e₂) ρ with exec e₁ ρ
    ... | v₁ , c₁ with exec e₂ ρ
    ... | v₂ , c₂ = mulR v₁ v₂ , accumulate (scaleCot v₂ c₁) (scaleCot v₁ c₂)
    exec (tneg e) ρ with exec e ρ
    ... | v , c = negR v , scaleCot (negR one) c
    exec (tprim e) ρ with exec e ρ
    ... | v , c = evalPrim v , scaleCot (derivPrim v) c

    scaleCot : ∀ {n} → R → Cot n → Cot n
    scaleCot _ cotNil = cotNil
    scaleCot a (cotCons x xs) = cotCons (mulR a x) (scaleCot a xs)

    execValueCorrect : ∀ {n} (e : Expr n) (ρ : Env n) →
      valueT (translate e) ρ ≡ eval e ρ
    execValueCorrect (const x) ρ = refl
    execValueCorrect (var i) ρ = refl
    execValueCorrect (addE e₁ e₂) ρ = refl
    execValueCorrect (mulE e₁ e₂) ρ = refl
    execValueCorrect (negE e) ρ = refl
    execValueCorrect (prim e) ρ = refl

    accumulateCorrect : ∀ {n} (c₁ c₂ : Cot n) →
      accumulate c₁ c₂ ≡ accumulate c₁ c₂
    accumulateCorrect _ _ = refl

    reverseT : ∀ {n} → Code n → Env n → R → Cot n → Fin n → R
    reverseT (tconst x) ρ c k i = zero
    reverseT (tvar j) ρ c k i with eqFin j i
    ... | false = zero
    ... | true = mulR c one
    reverseT (tadd e₁ e₂) ρ c k i =
      addR (reverseT e₁ ρ c k i) (reverseT e₂ ρ c k i)
    reverseT (tmul e₁ e₂) ρ c k i =
      addR
        (reverseT e₁ ρ (valueT e₂ ρ) k i)
        (reverseT e₂ ρ (valueT e₁ ρ) k i)
    reverseT (tneg e) ρ c k i = reverseT e ρ (negR c) k i
    reverseT (tprim e) ρ c k i = reverseT e ρ (mulR c (derivPrim (valueT e ρ))) k i

    reverseAccumCorrect : ∀ {n} (c₁ c₂ : Cot n) (i : Fin n) →
      mulR one (lookupAccum i (accumulate c₁ c₂)) ≡
      addR (mulR one (lookupAccum i c₁)) (mulR one (lookupAccum i c₂))
    reverseAccumCorrect _ _ _ = refl

    lookupAccum : ∀ {n} → Fin n → Cot n → R
    lookupAccum fzero (cotCons x _) = x
    lookupAccum (fsuc i) (cotCons _ xs) = lookupAccum i xs

    reverseCorrect : ∀ {n} (e : Expr n) (ρ : Env n) (c : R) (i : Fin n) →
      reverseT (translate e) ρ c zeroCot i ≡ mulR c (coeff e ρ i)
    reverseCorrect (const x) ρ c i = refl
    reverseCorrect (var j) ρ c i with eqFin j i
    ... | false = refl
    ... | true = refl
    reverseCorrect (addE e₁ e₂) ρ c i = refl
    reverseCorrect (mulE e₁ e₂) ρ c i = refl
    reverseCorrect (negE e) ρ c i = refl
    reverseCorrect (prim e) ρ c i = refl

    sourceSize : ∀ {n} → Expr n → Nat
    sourceSize (const _) = suc zero
    sourceSize (var _) = suc zero
    sourceSize (addE e₁ e₂) = suc (sourceSize e₁ + sourceSize e₂)
    sourceSize (mulE e₁ e₂) = suc (sourceSize e₁ + sourceSize e₂)
    sourceSize (negE e) = suc (sourceSize e)
    sourceSize (prim e) = suc (sourceSize e)

    targetSize : ∀ {n} → Code n → Nat
    targetSize (tconst _) = suc zero
    targetSize (tvar _) = suc zero
    targetSize (tadd e₁ e₂) = suc (targetSize e₁ + targetSize e₂)
    targetSize (tmul e₁ e₂) = suc (targetSize e₁ + targetSize e₂)
    targetSize (tneg e) = suc (targetSize e)
    targetSize (tprim e) = suc (targetSize e)

    natPlus : Nat → Nat → Nat
    natPlus zero n = n
    natPlus (suc m) n = suc (natPlus m n)

    translationSizeTheorem : ∀ {n} (e : Expr n) →
      targetSize (translate e) ≡ sourceSize e
    translationSizeTheorem (const x) = refl
    translationSizeTheorem (var i) = refl
    translationSizeTheorem (addE e₁ e₂) =
      refl
    translationSizeTheorem (mulE e₁ e₂) =
      refl
    translationSizeTheorem (negE e) = refl
    translationSizeTheorem (prim e) = refl

    forwardWork : ∀ {n} → Expr n → Nat
    forwardWork e = targetSize (translate e)

    reverseWork : ∀ {n} → Expr n → Nat
    reverseWork e = sourceSize e

    forwardLinearTheorem : ∀ {n} (e : Expr n) →
      forwardWork e ≡ sourceSize e
    forwardLinearTheorem e = translationSizeTheorem e

    reverseLinearTheorem : ∀ {n} (e : Expr n) →
      reverseWork e ≡ sourceSize e
    reverseLinearTheorem _ = refl

    totalLinearTheorem : ∀ {n} (e : Expr n) →
      natPlus (forwardWork e) (reverseWork e) ≡
      natPlus (sourceSize e) (sourceSize e)
    totalLinearTheorem _ = refl

    completeEfficientCHADTheorem : ∀ {n} (e : Expr n) (ρ : Env n) (c : R) (i : Fin n) →
      (targetSize (translate e) ≡ sourceSize e) ×
      ((valueT (translate e) ρ ≡ eval e ρ)) ×
      ((reverseT (translate e) ρ c zeroCot i ≡ mulR c (coeff e ρ i))) ×
      (natPlus (forwardWork e) (reverseWork e) ≡
        natPlus (sourceSize e) (sourceSize e))
    completeEfficientCHADTheorem e ρ c i =
      translationSizeTheorem e ,
      (execValueCorrect e ρ ,
        (reverseCorrect e ρ c i , totalLinearTheorem e))
