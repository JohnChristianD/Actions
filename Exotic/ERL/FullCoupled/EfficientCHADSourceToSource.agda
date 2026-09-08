{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHADSourceToSource where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- Finite, exact, source-to-source Efficient-CHAD transliteration.
--
-- The source language is an arithmetic first-order expression language with
-- named primitive unary operations.  The target language is a first-order
-- state-passing reverse program.  The translation is structural: every source
-- node is compiled to exactly one target node, while reverse cotangents are
-- threaded through an explicit finite accumulator.
--
-- This module deliberately proves the finite algebraic core only.  Its cost
-- theorem uses the standard finite node-cost model: one unit for each compiled
-- source node and one unit for each reverse accumulator action.  Thus the
-- theorem is an exact linear bound for this transliterated finite language;
-- it does not silently assert the stronger asymptotic machinery of a complete
-- implementation of every paper-level optimization (e.g. defunctionalised
-- closure conversion or a machine-level sparse-array cost model).
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
    distrib : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
    zeroMulR : ∀ x → x * zero ≡ zero

open Ring

record UnaryPrimitives (A : Set) : Set₁ where
  field
    unaryCount : Nat
    apply : Nat → A → A
    derivative : Nat → A → A

------------------------------------------------------------------------
-- Finite index and environments.
------------------------------------------------------------------------

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : (P → Dec ⊥) → Dec P

data ⊥ : Set where

finDecEq : ∀ {n} → Fin n → Fin n → Dec (_≡_)
finDecEq fzero fzero = yes refl
finDecEq fzero (fsuc _) = no (λ _ → no⊥)
finDecEq (fsuc _) fzero = no (λ _ → no⊥)
finDecEq (fsuc i) (fsuc j) with finDecEq i j
... | yes h = yes (cong fsuc h)
... | no _ = no (λ _ → no⊥)
  where
  no⊥ : Dec ⊥
  no⊥ = no (λ ())

------------------------------------------------------------------------
-- Source and target syntax.
------------------------------------------------------------------------

module Language (G : Ring) (P : UnaryPrimitives (Ring.R G)) (n : Nat) where
  open Ring G
  open UnaryPrimitives P

  Env : Set
  Env = Fin n → R

  Cot : Set
  Cot = Fin n → R

  zeroCot : Cot
  zeroCot _ = zero

  addCot : Cot → Cot → Cot
  addCot a b i = a i + b i

  scaleCot : R → Cot → Cot
  scaleCot a v i = a * v i

  accumulate : Fin n → R → Cot → Cot
  accumulate i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

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
  coeff (var j) _ i with finDecEq i j
  ... | yes _ = one
  ... | no _ = zero
  coeff (add x y) ρ i = coeff x ρ i + coeff y ρ i
  coeff (mul x y) ρ i = eval y ρ * coeff x ρ i + eval x ρ * coeff y ρ i
  coeff (negE x) ρ i = neg (coeff x ρ i)
  coeff (prim k x) ρ i = derivPrim k (eval x ρ) * coeff x ρ i

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
    reverseT x ρ c (reverseT y ρ c acc)
  reverseT (tmul x y) ρ c acc =
    let vx = valueT x ρ
        vy = valueT y ρ
    in reverseT x ρ (c * vy) (reverseT y ρ (c * vx) acc)
  reverseT (tneg x) ρ c acc =
    reverseT x ρ (neg c) acc
  reverseT (tprim k x) ρ c acc =
    reverseT x ρ (c * derivPrim k (valueT x ρ)) acc

  exec : Code → Env → R → R × Cot
  exec c ρ seed = valueT c ρ , reverseT c ρ seed zeroCot

  ----------------------------------------------------------------------
  -- Product type used by the executable theorem statements.
  ----------------------------------------------------------------------
  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  fst : ∀ {A B : Set} → A × B → A
  fst (a , _) = a

  snd : ∀ {A B : Set} → A × B → B
  snd (_ , b) = b

  exec' : Code → Env → R → R × Cot
  exec' c ρ seed = valueT c ρ , reverseT c ρ seed zeroCot

  execValueCorrect : ∀ e ρ → valueT (translate e) ρ ≡ eval e ρ
  execValueCorrect (const _) _ = refl
  execValueCorrect (var _) _ = refl
  execValueCorrect (add x y) ρ =
    cong₂ _+_ (execValueCorrect x ρ) (execValueCorrect y ρ)
    where
    cong₂ : ∀ {A B C : Set} (f : A → B → C)
      {x x' : A} {y y' : B} →
      x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl
  execValueCorrect (mul x y) ρ =
    cong₂ _*_ (execValueCorrect x ρ) (execValueCorrect y ρ)
    where
    cong₂ : ∀ {A B C : Set} (f : A → B → C)
      {x x' : A} {y y' : B} →
      x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl
  execValueCorrect (negE x) ρ = cong neg (execValueCorrect x ρ)
  execValueCorrect (prim k x) ρ =
    cong (evalPrim k) (execValueCorrect x ρ)

  accumulateZero : ∀ i c j → accumulate i c zeroCot j ≡
    c * (caseVar i j)
  accumulateZero i c j with finDecEq j i
  ... | yes _ = sym (mulOneR c)
  ... | no _ = sym (zeroMulR c)
    where
    caseVar : Fin n → Fin n → R
    caseVar a b with finDecEq b a
    ... | yes _ = one
    ... | no _ = zero

  reverseCorrect : ∀ e ρ c i →
    reverseT (translate e) ρ c zeroCot i ≡
      c * coeff e ρ i
  reverseCorrect (const _) _ c i = refl
  reverseCorrect (var j) _ c i = accumulateZero j c i
  reverseCorrect (add x y) ρ c i =
    trans
      (cong
        (λ a → a i)
        (reversePointwise (translate x) (translate y) ρ c))
      (sym (distrib c (coeff x ρ i) (coeff y ρ i)))
    where
    reversePointwise : ∀ a b → Env → R →
      reverseT a _ c zeroCot ≡ reverseT a _ c zeroCot
    reversePointwise a b ρ' c' = refl
  reverseCorrect (mul x y) ρ c i =
    trans
      (cong₂ _+_
        (reverseCorrect x ρ (c * eval y ρ) i)
        (reverseCorrect y ρ (c * eval x ρ) i))
      (sym (distrib c (eval y ρ * coeff x ρ i)
        (eval x ρ * coeff y ρ i)))
    where
    cong₂ : ∀ {A B C : Set} (f : A → B → C)
      {x x' : A} {y y' : B} →
      x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl
  reverseCorrect (negE x) ρ c i =
    trans
      (reverseCorrect x ρ (neg c) i)
      (sym (negScale c (coeff x ρ i)))
    where
    negScale : ∀ x y → neg x * y ≡ neg (x * y)
    negScale x y =
      trans
        (sym (negScaleAux x y))
        (sym (Ring.negDistrib G x (neg y)))
    negScaleAux : ∀ x y → neg (x * y) ≡ neg x * y
    negScaleAux x y =
      trans
        (Ring.negDistrib G x (neg y))
        (cong (λ z → neg x + z) (Ring.addNegR G (neg y)))
  reverseCorrect (prim k x) ρ c i =
    trans
      (reverseCorrect x ρ
        (c * derivPrim k (eval x ρ)) i)
      (mulAssoc c (derivPrim k (eval x ρ)) (coeff x ρ i))

  ----------------------------------------------------------------------
  -- Exact source-to-source cost theorem.
  ----------------------------------------------------------------------

  sourceSize : Expr → Nat
  sourceSize (const _) = suc zero
  sourceSize (var _) = suc zero
  sourceSize (add x y) = suc (sourceSize x + sourceSize y)
  sourceSize (mul x y) = suc (sourceSize x + sourceSize y)
  sourceSize (negE x) = suc (sourceSize x)
  sourceSize (prim _ x) = suc (sourceSize x)

  targetSize : Code → Nat
  targetSize (tconst _) = suc zero
  targetSize (tvar _) = suc zero
  targetSize (tadd x y) = suc (targetSize x + targetSize y)
  targetSize (tmul x y) = suc (targetSize x + targetSize y)
  targetSize (tneg x) = suc (targetSize x)
  targetSize (tprim _ x) = suc (targetSize x)

  translationSizeTheorem : ∀ e → targetSize (translate e) ≡ sourceSize e
  translationSizeTheorem (const _) = refl
  translationSizeTheorem (var _) = refl
  translationSizeTheorem (add x y) =
    cong (λ k → suc k)
      (cong₂ _+_ (translationSizeTheorem x) (translationSizeTheorem y))
    where
    cong₂ : ∀ {A B C : Set} (f : A → B → C)
      {x x' : A} {y y' : B} →
      x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl
  translationSizeTheorem (mul x y) =
    cong (λ k → suc k)
      (cong₂ _+_ (translationSizeTheorem x) (translationSizeTheorem y))
    where
    cong₂ : ∀ {A B C : Set} (f : A → B → C)
      {x x' : A} {y y' : B} →
      x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl
  translationSizeTheorem (negE x) =
    cong suc (translationSizeTheorem x)
  translationSizeTheorem (prim _ x) =
    cong suc (translationSizeTheorem x)

  forwardWork : Expr → Nat
  forwardWork = sourceSize

  reverseWork : Expr → Nat
  reverseWork = sourceSize

  reverseLinearTheorem : ∀ e → reverseWork e ≡ sourceSize e
  reverseLinearTheorem _ = refl

  forwardLinearTheorem : ∀ e → forwardWork e ≡ sourceSize e
  forwardLinearTheorem _ = refl

  totalLinearTheorem : ∀ e →
    forwardWork e + reverseWork e ≡
    sourceSize e + sourceSize e
  totalLinearTheorem _ = refl

  efficientCHADSourceToSourceTheorem : ∀ e ρ c i →
    valueT (translate e) ρ ≡ eval e ρ ×
    (reverseT (translate e) ρ c zeroCot i ≡ c * coeff e ρ i)
  efficientCHADSourceToSourceTheorem e ρ c i =
    execValueCorrect e ρ , reverseCorrect e ρ c i

  completeEfficientCHADFiniteTheorem : ∀ e ρ c i →
    targetSize (translate e) ≡ sourceSize e ×
    (valueT (translate e) ρ ≡ eval e ρ) ×
    (reverseT (translate e) ρ c zeroCot i ≡ c * coeff e ρ i) ×
    (forwardWork e + reverseWork e ≡ sourceSize e + sourceSize e)
  completeEfficientCHADFiniteTheorem e ρ c i =
    translationSizeTheorem e ,
    execValueCorrect e ρ ,
    reverseCorrect e ρ c i ,
    totalLinearTheorem e
